-- Prove2me | Theorems.Thm_GlobalTheory_ArcAvoid_exists_injective_of_height_le_one
-- name    : GlobalTheory.ArcAvoid.exists_injective_of_height_le_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:58:29.950051+00:00
-- url     : https://prove2.me/theorems/0b377b34-33c5-46ba-9500-d86eb727c735
-- title:
--   Arc Avoid: exists injective of height le one
-- statement:
--   The Arc Avoid construction uses the exists injective of height le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRingEquivPowerSeriesOfComplete.lean#L93-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRingEquivPowerSeriesOfComplete.lean#L93-L146

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
open Polynomial

theorem GlobalTheory.ArcAvoid.exists_injective_of_height_le_one {k B : Type*} [Field k] [IsAlgClosed k] [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (m : Ideal B) [hm : m.IsMaximal]
    (h1 : m.height ≤ 1) :
    ∃ φ : B →ₐ[k] PowerSeries k, Function.Injective φ ∧
      ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by sorry
