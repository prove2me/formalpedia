-- Prove2me | Theorems.Thm_GlobalTheory_TorsionZero_aeval_eq_zero_iff_components
-- name    : GlobalTheory.TorsionZero.aeval_eq_zero_iff_components
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:08:53.381633+00:00
-- url     : https://prove2.me/theorems/477051f9-6f52-496c-a51d-b929914dbc0d
-- title:
--   Torsion Zero: aeval eq zero iff components
-- statement:
--   The Torsion Zero construction uses the aeval eq zero iff components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L54-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L54-L72

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
variable {K σ : Type} [Field K]

theorem GlobalTheory.TorsionZero.aeval_eq_zero_iff_components {R : Type} [CommRing R] [Algebra K R] (𝒜 : ℕ → Submodule K R)
    [GradedAlgebra 𝒜] {x : σ → R} (hx : ∀ j, x j ∈ 𝒜 1) (G : MvPolynomial σ K) :
    aeval x G = 0 ↔ ∀ n, aeval x (homogeneousComponent n G) = 0 := by sorry
