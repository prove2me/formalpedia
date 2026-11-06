-- Prove2me | Theorems.Thm_MatrixLeeSidford_eq_5_23
-- name    : MatrixLeeSidford.eq_5_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:35.121193+00:00
-- url     : https://prove2.me/theorems/48130477-569c-4c36-a0b6-297a299b4a79
-- title:
--   Eq. (5.23) — lower bound $2\Phi_p(y)\ge\log\det L_y^*(I)-n(1-1/s)$
-- statement:
--   Throughout, $A_1,\dots,A_m,C$ are real symmetric $n\times n$ matrices satisfying the standing assumptions (4.3): $\Omega=\{y:S(y)\succ0\}\neq\emptyset$, the $A_i$ are linearly independent, and $\bigcap_i\ker A_i=\{0\}$.
--
--   Let $s\ge2$ be an integer and $y\in\Omega$. Then
--   $$
--   2\Phi_p(y)\ \ge\ \log\det L_y^*(I)-n\Big(1-\frac1s\Big).
--   $$
--   It is the bound used to show that the barrier diverges at the boundary of $\Omega$: as $y$ approaches the boundary, the largest eigenvalue of $L_y^*(I)$ diverges while its smallest stays bounded away from $0$.
--
--   Differences from the source:
--   - encoding: Aᵢ, C ∈ Sⁿ, y, h ∈ ℝᵐ → real n×n matrices with IsHermitian hypotheses; y, h ∈ EuclideanSpace ℝ (Fin m); reason: Lean representation of the same objects
--   - generalization: s := 2⌈log(2mn)⌉ (Definition 5.1, Section 5) → every integer s ≥ 2; reason: (5.23) is the dual formulation (4.9) of Lemma 4.4 at W = I, valid for every integer s ≥ 2; it specializes at s = sParam m n
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Eq. (5.23), p.47

import Mathlib
import Definitions.Def_MatrixLeeSidford_Phi__87229e
import Definitions.Def_MatrixLeeSidford_Ladj
import Definitions.Def_MatrixLeeSidford_dualRegion

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Eq. (5.23)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.47). For every `y ∈ Ω`, `2Φ_p(y) ≥ log det L_y^*(I) − n(1 − 1/s)`.

**Formalization Note** The standing assumptions (4.3) (p.32) are hypotheses: `Aᵢ, C` symmetric, `Ω ≠ ∅`, the `Aᵢ`
linearly independent, `⋂ᵢ ker Aᵢ = {0}`. Stated for every integer `s ≥ 2` (it is (4.9) at the trial
point `W = I`, valid for every such `s`). -/
theorem eq_5_23 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0)
    (s : ℕ) (hs : 2 ≤ s) (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ dualRegion A C) :
    Real.log (Ladj A (slack A C y) 1).det - (n : ℝ) * (1 - 1 / (s : ℝ)) ≤ 2 * Phi A C s y := by sorry

end MatrixLeeSidford
