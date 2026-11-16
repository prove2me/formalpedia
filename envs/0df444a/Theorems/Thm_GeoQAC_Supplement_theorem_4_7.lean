-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_4_7
-- name    : GeoQAC.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:28:43.700801+00:00
-- url     : https://prove2.me/theorems/3bd4e6ec-ce09-4128-b2da-b12bcec6b21f
-- title:
--   Theorem 4.7 — exact cat-state synthesis at depths $\lceil\log_2n\rceil$, $O(\log n/\log\log n)$, $O(d)$
-- statement:
--   1. **(a)** For every $n\ge2$ there is a $[1,n]$-2D-QAC circuit (exactly $n$ qubits, no ancillas) of depth at most $\lceil\log_2n\rceil$ that synthesizes $|\mathrm{cat}_n\rangle$ exactly.
--   2. **(b)** There are $C_0>0$, an exponent $e$ and $N$ such that for every $n\ge N$ some $[w,h]$-2D-QAC circuit with $w,h\le C_0n^e$ and depth at most $C_0\log n/\log\log n$ synthesizes $|\mathrm{cat}_n\rangle$ exactly.
--   3. **(c)** There is $C_0>0$ such that for every $n\ge2$ and every integer $1\le d\le\log_2n$ some $[w,h]$-2D-QAC circuit with depth at most $C_0d$,
--   $$
--   w\le C_0\,d\,n^{1/d},\qquad h\le\exp\big(C_0\,n^{1/d}\log n\big),
--   $$
--   synthesizes $|\mathrm{cat}_n\rangle$ exactly.
--
--   Exact synthesis means target-marginal fidelity $1$ from $|0\cdots0\rangle$, with the targets at positions chosen with the circuit. Part (c) matches the lower bound of Theorem 3.8.
--
--   Differences from the source:
--   - reading: (b) for n ≥ 2 with depth O(log n / log log n) → for n ≥ N; reason: log n / log log n is not positive for small n, so the bound is asymptotic
--   - encoding: poly(n); 1 ≤ d ≤ log₂ n → ≤ C₀ n^e; 1 ≤ d ∧ 2^d ≤ n; reason: same conditions
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 4.7, p.33

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_Supplement_targetFidelity
import Definitions.Def_GeoQAC_Supplement_catVec

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem 4.7** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.33). "For `n ≥ 2`, the
`n`-qubit cat state admits exact synthesis by the following circuits:
(a) A depth-`⌈log₂ n⌉` `[1, n]`-2D-QAC circuit with no ancillas.
(b) A depth-`O(log n / log log n)` `[poly(n), poly(n)]`-2D-QAC circuit.
(c) For every integer `1 ≤ d ≤ log₂ n`, a depth-`O(d)` `[O(d n^{1/d}), exp(O(n^{1/d} log n))]`-2D-QAC
circuit."

**Formalization Note.**
* Exact synthesis is target-marginal fidelity `1` (Definition 2.6) from `|0…0⟩`, with the `n` targets
  at an injective placement `tgt` chosen with the circuit.
* (a) The grid `Pos 1 n` has exactly `n` qubits (no ancillas) and the depth is at most
  `⌈log₂ n⌉ = Nat.clog 2 n`, with no constant.
* (b) is stated for `n ≥ N` (`log n / log log n` is not positive for small `n`), `poly(n)` as
  `≤ C₀ n^e`. (c): one absolute `C₀`; `1 ≤ d ≤ log₂ n` is `1 ≤ d ∧ 2^d ≤ n`. `log` is natural. -/
theorem theorem_4_7 :
    (∀ n : ℕ, 2 ≤ n → ∃ (D : ℕ) (C : QACCircuit (Pos 1 n) D) (tgt : Fin n ↪ Pos 1 n),
      C.Is2D ∧ D ≤ Nat.clog 2 n ∧ targetFidelity C tgt (catVec n) = 1) ∧
    (∃ (C₀ e : ℝ) (N : ℕ), 0 < C₀ ∧ ∀ n : ℕ, N ≤ n →
      ∃ (w h D : ℕ) (C : QACCircuit (Pos w h) D) (tgt : Fin n ↪ Pos w h),
        C.Is2D ∧ (w : ℝ) ≤ C₀ * (n : ℝ) ^ e ∧ (h : ℝ) ≤ C₀ * (n : ℝ) ^ e ∧
        (D : ℝ) ≤ C₀ * Real.log n / Real.log (Real.log n) ∧
        targetFidelity C tgt (catVec n) = 1) ∧
    (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 2 ≤ n → ∀ d : ℕ, 1 ≤ d → 2 ^ d ≤ n →
      ∃ (w h D : ℕ) (C : QACCircuit (Pos w h) D) (tgt : Fin n ↪ Pos w h),
        C.Is2D ∧ (D : ℝ) ≤ C₀ * d ∧ (w : ℝ) ≤ C₀ * d * (n : ℝ) ^ ((1 : ℝ) / d) ∧
        (h : ℝ) ≤ Real.exp (C₀ * (n : ℝ) ^ ((1 : ℝ) / d) * Real.log n) ∧
        targetFidelity C tgt (catVec n) = 1) := by sorry

end GeoQAC.Supplement
