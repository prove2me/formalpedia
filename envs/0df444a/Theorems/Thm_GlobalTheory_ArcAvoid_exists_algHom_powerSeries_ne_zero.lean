-- Prove2me | Theorems.Thm_GlobalTheory_ArcAvoid_exists_algHom_powerSeries_ne_zero
-- name    : GlobalTheory.ArcAvoid.exists_algHom_powerSeries_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:58:38.870707+00:00
-- url     : https://prove2.me/theorems/3290835e-e5fb-47fd-9d78-e86fa2cc8706
-- title:
--   Arc Avoid: exists alg Hom power Series ne zero
-- statement:
--   The Arc Avoid construction uses the exists alg Hom power Series ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRingEquivPowerSeriesOfComplete.lean#L148-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRingEquivPowerSeriesOfComplete.lean#L148-L169

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_StalkGenericPointSpecializesOfSpecializes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingEquivPowerSeriesOfComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.ArcAvoid

theorem GlobalTheory.ArcAvoid.exists_algHom_powerSeries_ne_zero :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (m : Ideal B), m.IsMaximal → ∀ f : B, f ≠ 0 →
      ∃ φ : B →ₐ[k] PowerSeries k, φ f ≠ 0 ∧
        ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by sorry
