-- Prove2me | Theorems.Thm_GlobalTheory_TorsionZero_nonempty_gradedAlgebra_subGrading
-- name    : GlobalTheory.TorsionZero.nonempty_gradedAlgebra_subGrading
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:08:45.162741+00:00
-- url     : https://prove2.me/theorems/4db1700a-9960-41df-9684-9a6ba2877e70
-- title:
--   Torsion Zero: nonempty graded Algebra sub Grading
-- statement:
--   The Torsion Zero construction uses the nonempty graded Algebra sub Grading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L175-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L175-L224

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K R : Type} [Field K] [CommRing R] [Algebra K R]

theorem GlobalTheory.TorsionZero.nonempty_gradedAlgebra_subGrading (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜] {N : ℕ}
    (hN : 1 ≤ N) (S : Set R) (hS : ∀ y ∈ S, ∃ e, y ∈ 𝒜 (N * e)) :
    Nonempty (GradedAlgebra (subGrading 𝒜 N (Algebra.adjoin K S))) := by sorry
