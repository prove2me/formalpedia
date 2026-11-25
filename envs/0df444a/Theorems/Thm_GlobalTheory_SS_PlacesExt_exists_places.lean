-- Prove2me | Theorems.Thm_GlobalTheory_SS_PlacesExt_exists_places
-- name    : GlobalTheory.SS.PlacesExt.exists_places
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:14:51.069546+00:00
-- url     : https://prove2.me/theorems/ced33e9d-afdc-436f-aa91-f38aebfd6b2b
-- title:
--   Places Ext: exists places
-- statement:
--   The Places Ext construction uses the exists places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsProductFormulaPlacesFunctionField.lean#L229-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsProductFormulaPlacesFunctionField.lean#L229-L248

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PlacesExt
open IsDedekindDomain Polynomial ReciprocityTheory.ChartRestriction.G.T0

theorem GlobalTheory.SS.PlacesExt.exists_places : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (t : K), Transcendental k t →
    FiniteDimensional (IntermediateField.adjoin k {t}) K →
    Algebra.IsSeparable (IntermediateField.adjoin k {t}) K →
    ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → IsAlgebraic k x := by sorry
