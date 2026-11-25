-- Prove2me | Theorems.Thm_GlobalTheory_SpreadScheme_hasModel_of_two
-- name    : GlobalTheory.SpreadScheme.hasModel_of_two
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:04:54.2676+00:00
-- url     : https://prove2.me/theorems/f2dbc795-7ddf-4fb6-af67-d28c739e21b4
-- title:
--   Spread Scheme: has Model of two
-- statement:
--   The Spread Scheme construction uses the has Model of two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L316-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L316-L345

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SpreadScheme
open GlobalTheory.Spread GlobalTheory.GlueModels
attribute [instance] PairModel.lfp PairModel.qs PairModel.qc PairModel.opn PairModel.qca
variable {S S₁ S₀ U T : Scheme.{0}} {f : S ⟶ S₀} {p : U ⟶ S} {a : T ⟶ U}
variable {V : Type} [CommRing V]

theorem GlobalTheory.SpreadScheme.hasModel_of_two {X W : Scheme.{0}} (q : X ⟶ Sp V) [QuasiSeparated q] (u : U ⟶ X) (v : W ⟶ X)
    [IsOpenImmersion u] [IsOpenImmersion v] (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    [CompactSpace U] [CompactSpace W] (hU : HasModel (u ≫ q)) (hW : HasModel (v ≫ q)) : HasModel q := by sorry
