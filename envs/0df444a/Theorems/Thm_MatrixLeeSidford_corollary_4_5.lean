-- Prove2me | Theorems.Thm_MatrixLeeSidford_corollary_4_5
-- name    : MatrixLeeSidford.corollary_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:25.411115+00:00
-- url     : https://prove2.me/theorems/9817965c-bbf3-4abd-adfb-da90e2aae1c3
-- title:
--   Corollary 4.5 — volume interpretation and $m^{-1/(2s)}E_{G_*}\subseteq K_y$
-- statement:
--   Throughout, $A_1,\dots,A_m,C$ are real symmetric $n\times n$ matrices satisfying the standing assumptions (4.3): $\Omega=\{y:S(y)\succ0\}\neq\emptyset$, the $A_i$ are linearly independent, and $\bigcap_i\ker A_i=\{0\}$.
--
--   Let $s\ge2$ be an integer and $y\in\Omega$. Then
--   $$
--   \Phi_p(y)=-\frac12\log\det G_*(y)+\frac m{2s}-\frac m2,\qquad m^{-1/(2s)}E_{G_*(y)}\subseteq K_y .
--   $$
--   Up to an additive constant depending on $m$ and $s$, the potential is the negative log-volume of an ellipsoid inscribed in the symmetrized local region.
--
--   Differences from the source:
--   - encoding: Aᵢ, C ∈ Sⁿ, y, h ∈ ℝᵐ → real n×n matrices with IsHermitian hypotheses; y, h ∈ EuclideanSpace ℝ (Fin m); reason: Lean representation of the same objects
--   - encoding: G_*(y), the unique minimizer of f_y → optWeightAt / optWeight, a chosen minimizer (junk 0 if none exists); reason: by Lemma 4.4 the minimizer exists and is unique under (4.3), so the chosen one is G_*
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Corollary 4.5, p.36

import Mathlib
import Definitions.Def_MatrixLeeSidford_optWeightAt
import Definitions.Def_MatrixLeeSidford_Phi__87229e
import Definitions.Def_MatrixLeeSidford_ellipsoid
import Definitions.Def_MatrixLeeSidford_localRegion
import Definitions.Def_MatrixLeeSidford_dualRegion

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Corollary 4.5 (Volume interpretation)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.36). Let `y ∈ Ω`. Then
`Φ_p(y) = −½ log det G_*(y) + m/(2s) − m/2` and `m^{−1/(2s)} E_{G_*(y)} ⊆ K_y`.

**Formalization Note** The standing assumptions (4.3) (p.32) are hypotheses: `Aᵢ, C` symmetric, `Ω ≠ ∅`, the `Aᵢ`
linearly independent, `⋂ᵢ ker Aᵢ = {0}`. `s ≥ 2` integer; `G_*(y)` is `optWeightAt`. -/
theorem corollary_4_5 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0)
    (s : ℕ) (hs : 2 ≤ s) (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ dualRegion A C) :
    Phi A C s y = -(1 / 2) * Real.log (optWeightAt A C s y).det + (m : ℝ) / (2 * (s : ℝ)) - (m : ℝ) / 2 ∧
    ((m : ℝ) ^ (-(1 / (2 * (s : ℝ))))) • ellipsoid (optWeightAt A C s y) ⊆
      localRegion A (slack A C y) := by sorry

end MatrixLeeSidford
