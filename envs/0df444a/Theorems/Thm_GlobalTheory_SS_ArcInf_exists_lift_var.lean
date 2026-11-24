-- Prove2me | Theorems.Thm_GlobalTheory_SS_ArcInf_exists_lift_var
-- name    : GlobalTheory.SS.ArcInf.exists_lift_var
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:34:10.398866+00:00
-- url     : https://prove2.me/theorems/8e232a25-6b64-4f44-bfb8-8573c9203566
-- title:
--   Arc Inf: exists lift var
-- statement:
--   The Arc Inf construction uses the exists lift var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ArcExtendsOfRegularSecondAxis.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ArcExtendsOfRegularSecondAxis.lean#L18-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalRingSecondVariable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFactorOfRangeSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ArcExtendsOfRegularSecondAxis
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
open GlobalTheory.SS.ArcInf
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf

theorem GlobalTheory.SS.ArcInf.exists_lift_var (k : Type) [Field k] (n : Fin 2) :
    ∃ σ : FractionRing (PowerSeries k) →ₐ[k] FractionRing (MvPowerSeries (Fin 2) k),
      ∀ x : PowerSeries k, σ (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _
        (x.subst (MvPowerSeries.X n : MvPowerSeries (Fin 2) k)) := by sorry
