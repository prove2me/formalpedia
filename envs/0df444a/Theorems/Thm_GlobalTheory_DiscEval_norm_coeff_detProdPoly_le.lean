-- Prove2me | Theorems.Thm_GlobalTheory_DiscEval_norm_coeff_detProdPoly_le
-- name    : GlobalTheory.DiscEval.norm_coeff_detProdPoly_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:00:17.269713+00:00
-- url     : https://prove2.me/theorems/947d1081-4df1-419e-b2c2-62c4390b6d8f
-- title:
--   Disc Eval: norm coeff det Prod Poly le
-- statement:
--   The Disc Eval construction uses the norm coeff det Prod Poly le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L280-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L280-L290

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
open MvPolynomial
variable {O : Type*} [CommRing O] {π : O}
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem GlobalTheory.DiscEval.norm_coeff_detProdPoly_le {ι : Type*} [Fintype ι] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] (μ : EntryIndex n n →₀ ℕ) : ‖coeff μ (detProdPoly K n)‖ ≤ 1 := by sorry
