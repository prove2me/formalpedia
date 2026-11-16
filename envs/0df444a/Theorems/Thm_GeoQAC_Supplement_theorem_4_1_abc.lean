-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_4_1_abc
-- name    : GeoQAC.Supplement.theorem_4_1_abc
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:26:38.427938+00:00
-- url     : https://prove2.me/theorems/c7495675-a79f-46d5-97c8-e6de8ab57c5e
-- title:
--   Theorem 4.1(a)–(c) — clean parity at depths $O(n)$, $O(\log n)$, $O(\log n/\log\log n)$
-- statement:
--   There is an absolute constant $C_0>0$ such that:
--
--   1. **(a)** for every $n\ge2$ there is an exact clean implementation of $U_{\oplus n}$ by a $[1,n+1]$-2D-QAC circuit (exactly the $n+1$ logical qubits, no ancillas) of depth at most $C_0 n$;
--   2. **(b)** for every $n\ge2$ there is one by a $[2,n+1]$-2D-QAC circuit of depth at most $C_0\log n$;
--   3. **(c)** there are $N$ and an exponent $e$ such that for every $n\ge N$ there is one by a $[w,h]$-2D-QAC circuit with $w,h\le C_0n^e$ and depth at most $C_0\log n/\log\log n$.
--
--   Part (d), the narrow constant-depth construction, is the second half of the mission's goal.
--
--   Differences from the source:
--   - reading: (c) for n ≥ 2 with depth O(log n / log log n) → for n ≥ N; reason: log n / log log n is not positive for small n, so the bound is asymptotic
--   - encoding: poly(n) → ≤ C₀ n^e for one exponent e; reason: definition of a polynomial bound (§2.1)
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 4.1(a)–(c), p.30

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_IsCleanImpl

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem 4.1 (a)–(c)** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.30). "For
`n ≥ 2`, the parity unitary on `n` controls has the following exact clean implementations:
(a) A depth-`O(n)` `[1, n + 1]`-2D-QAC circuit with no ancillas.
(b) A depth-`O(log n)` `[2, n + 1]`-2D-QAC circuit.
(c) A depth-`O(log n / log log n)` `[poly(n), poly(n)]`-2D-QAC circuit."
Part (d) is the second conjunct of the base mission's goal `GeoQAC.parity_width_tradeoff`.

**Formalization Note.**
* One absolute constant `C₀` for all three parts. Exact clean implementation of `U_⊕n` is the
  published `GeoQAC.IsCleanParity` (ancillas `|0⟩` in and out, one global phase, logical qubits
  anywhere on the grid).
* (a) The grid `Pos 1 (n+1)` has exactly the `n + 1` logical qubits, so there are no ancillas.
* (c) `log n / log log n` is not positive for small `n`, so (c) is stated for `n ≥ N`
  (asymptotic notation); `poly(n)` is `≤ C₀ n^e` for one exponent `e`.
* `log` is the natural logarithm (p.9: any fixed base). -/
theorem theorem_4_1_abc : ∃ C₀ : ℝ, 0 < C₀ ∧
    (∀ n : ℕ, 2 ≤ n → ∃ (D : ℕ) (C : QACCircuit (Pos 1 (n + 1)) D)
      (ctrl : Fin n ↪ Pos 1 (n + 1)) (acc : Pos 1 (n + 1)),
      C.Is2D ∧ (D : ℝ) ≤ C₀ * n ∧ IsCleanParity C ctrl acc) ∧
    (∀ n : ℕ, 2 ≤ n → ∃ (D : ℕ) (C : QACCircuit (Pos 2 (n + 1)) D)
      (ctrl : Fin n ↪ Pos 2 (n + 1)) (acc : Pos 2 (n + 1)),
      C.Is2D ∧ (D : ℝ) ≤ C₀ * Real.log n ∧ IsCleanParity C ctrl acc) ∧
    (∃ (N : ℕ) (e : ℝ), ∀ n : ℕ, N ≤ n → ∃ (w h D : ℕ) (C : QACCircuit (Pos w h) D)
      (ctrl : Fin n ↪ Pos w h) (acc : Pos w h),
      C.Is2D ∧ (w : ℝ) ≤ C₀ * (n : ℝ) ^ e ∧ (h : ℝ) ≤ C₀ * (n : ℝ) ^ e ∧
      (D : ℝ) ≤ C₀ * Real.log n / Real.log (Real.log n) ∧ IsCleanParity C ctrl acc) := by sorry

end GeoQAC.Supplement
