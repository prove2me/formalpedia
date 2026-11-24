-- Prove2me | Theorems.Thm_GlobalTheory_SS_Height_gs_pw
-- name    : GlobalTheory.SS.Height.gs_pw
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:34:46.293059+00:00
-- url     : https://prove2.me/theorems/fc496eb4-2048-4172-9635-61c199bdd460
-- title:
--   Height: gs pw
-- statement:
--   The Height construction uses the gs pw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleHeightProperScheme.lean#L166-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleHeightProperScheme.lean#L166-L172

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Height
open IsLocalRing
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (Pl : Places k K)

theorem GlobalTheory.SS.Height.gs_pw {X Y : Scheme.{0}} {L : LB X} {N : ℤ} (s : LB.Sec (GlobalTheory.AbLaw.pw L N)) (x : Y ⟶ X) (y : Y)
    {i j : L.ι} (hi : x y ∈ L.U i) (hj : x y ∈ L.U j) :
    gs x y (L.U i) (s.f i) = (gm x y (L.U i ⊓ L.U j) (L.g i j) ^ N).val * gs x y (L.U j) (s.f j) := by sorry
