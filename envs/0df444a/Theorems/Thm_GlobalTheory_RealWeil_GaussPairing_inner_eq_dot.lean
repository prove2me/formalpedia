-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_GaussPairing_inner_eq_dot
-- name    : GlobalTheory.RealWeil.GaussPairing.inner_eq_dot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:33.743235+00:00
-- url     : https://prove2.me/theorems/0231963e-18e7-4f0d-9ad5-762703f478f6
-- title:
--   Gauss Pairing: inner eq dot
-- statement:
--   The Gauss Pairing construction uses the inner eq dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianPairingUnitaryGroupTwoThree.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianPairingUnitaryGroupTwoThree.lean#L24-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingOfNormSqEqSumComplexCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.GaussPairing
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type} [Fintype ι]

theorem GlobalTheory.RealWeil.GaussPairing.inner_eq_dot (e : V ≃L[ℝ] (ι → ℂ)) (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) (x y : V) :
    ((⟪x, y⟫ : ℝ) : ℂ) = (1 / 2 : ℂ) * (star (e x) ⬝ᵥ e y + star (e y) ⬝ᵥ e x) := by sorry
