-- Prove2me | Theorems.Thm_GeoQAC_parity_width_tradeoff
-- name    : GeoQAC.parity_width_tradeoff
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:35.867198+00:00
-- url     : https://prove2.me/theorems/61f946d3-be51-4a97-a039-9a1a89e48c9c
-- title:
--   Theorems 3.16 and 4.1(d) — PARITY in 2D-QAC has the tight width–depth tradeoff $w=n^{\Theta(1/d)}$
-- statement:
--   PARITY computation has a tight width–depth tradeoff of $w=n^{\Theta(1/d)}$ in the constant-depth regime when the circuit may use arbitrarily many ancillas. Precisely:
--
--   1. **(Theorem 3.16, first sentence)** $\mathrm{as}(\mathrm{PARITY}_n)=n$ for every $n$.
--   2. **(Theorem 3.16, lower bound)** For every fixed depth $d\ge1$ there is $c_d>0$ such that every depth-$d$ $[w,h]$-2D-QAC circuit that computes $\mathrm{PARITY}_n$ exactly from product ancillas has
--   $$
--   w\ge c_d\, n^{1/(6d+1)} .
--   $$
--   This holds for every $n$, every grid length $h$, every placement of the inputs, every output qubit and every product ancilla state.
--   3. **(Theorem 4.1(d), upper bound)** There is an absolute constant $C_0$ such that for every $n\ge2$ and every integer $1\le d\le\log_2 n$ there is an exact clean implementation of the parity unitary $U_{\oplus n}$ on $n$ controls by a $[w,h]$-2D-QAC circuit of depth at most $C_0d$ with
--   $$
--   w\le C_0\,d\,n^{1/d},\qquad h\le\exp\big(C_0\,n^{1/d}\log n\big).
--   $$
--
--   The depth counts multi-qubit layers only. The lower bound allows garbage; the upper bound restores all ancillas to $|0\rangle$ up to a fixed global phase.
--
--   Differences from the source:
--   - encoding: $\Omega(\cdot)$ "for fixed depth $d$" → $\forall d\ge1\ \exists c>0$, $c$ chosen after $d$ and before everything else; reason: §2.1, p.9 (dependence on fixed parameters is allowed when stated) and "For fixed depth $d\ge1$".
--   - encoding: $O(\cdot)$ in Theorem 4.1(d) → one absolute $C_0$ chosen before $n$ and $d$, natural logarithm; reason: §2.1, p.9.
--   - encoding: integer $1\le d\le\log_2 n$ → $1\le d$ and $2^d\le n$; reason: equivalent for integers.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), abstract p.1; Table 1, p.5; Theorem 3.16, p.26; Theorem 4.1(d), p.30

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_ComputesExactly
import Definitions.Def_GeoQAC_IsCleanImpl
import Definitions.Def_GeoQAC_avgSens

namespace GeoQAC

/-- **The PARITY width–depth tradeoff** (arXiv:2604.07178, version of 2026-11-03, abstract p.1: "PARITY
computation has a tight width–depth tradeoff of `w = n^{Θ(1/d)}` in the constant-depth regime if the
circuit allows arbitrarily many ancillas"; Table 1, p.5, cites Theorems 3.16 and 4.1). The conjunction
of
* **Theorem 3.16** (p.26): "The parity function satisfies `as(PARITY_n) = n`. For fixed depth
  `d ≥ 1`, exact computation of `PARITY_n` requires `w = Ω(n^{1/(6d+1)})`" (§3.5: exact computation in
  the 2D-QAC model, with product ancillas); and
* **Theorem 4.1(d)** (p.30): "For `n ≥ 2`, the parity unitary on `n` controls has … exact clean
  implementations: (d) For every integer `1 ≤ d ≤ log₂ n`, a depth-`O(d)`
  `[O(d n^{1/d}), exp(O(n^{1/d} log n))]`-2D-QAC circuit."

**Formalization Note.**
* Lower bound: `c` may depend on the fixed `d` (chosen after `d`), but not on `n`, the grid, the input
  placement `inp` (any injective map), the output qubit `out` (any qubit) or the product ancilla state
  `anc`. Depth counts multi-qubit layers only; garbage is allowed.
* Upper bound: `C₀` is absolute (chosen before `n` and `d`); `1 ≤ d ≤ log₂ n` is `1 ≤ d ∧ 2^d ≤ n`;
  the circuit is an exact clean implementation of `U_⊕n` (ancillas `|0⟩`, one global phase);
  `log` is the natural logarithm (p.9: any fixed base). -/
theorem parity_width_tradeoff :
    (∀ n : ℕ, avgSens (parityFn n) = n) ∧
    (∀ d : ℕ, 1 ≤ d → ∃ c : ℝ, 0 < c ∧
      ∀ (n w h : ℕ) (C : QACCircuit (Pos w h) d) (inp : Fin n ↪ Pos w h)
        (anc : Pos w h → Bool → ℂ) (out : Pos w h),
        C.Is2D → ComputesExactly C inp anc out (parityFn n) →
          c * (n : ℝ) ^ ((1 : ℝ) / (6 * (d : ℝ) + 1)) ≤ w) ∧
    (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 2 ≤ n → ∀ d : ℕ, 1 ≤ d → 2 ^ d ≤ n →
      ∃ (w h D : ℕ) (C : QACCircuit (Pos w h) D) (ctrl : Fin n ↪ Pos w h) (acc : Pos w h),
        C.Is2D ∧ (D : ℝ) ≤ C₀ * d ∧ (w : ℝ) ≤ C₀ * d * (n : ℝ) ^ ((1 : ℝ) / d) ∧
        (h : ℝ) ≤ Real.exp (C₀ * (n : ℝ) ^ ((1 : ℝ) / d) * Real.log n) ∧
        IsCleanParity C ctrl acc) := by sorry

end GeoQAC
