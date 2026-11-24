-- Prove2me | Theorems.Thm_GlobalTheory_PhiSpec_gs_of_charts
-- name    : GlobalTheory.PhiSpec.gs_of_charts
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:46:18.461798+00:00
-- url     : https://prove2.me/theorems/ec2bd332-7eca-4159-9e63-f9ade09bff16
-- title:
--   Phi Spec: gs of charts
-- statement:
--   The Phi Spec construction uses the gs of charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiSpecialises.lean#L191-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiSpecialises.lean#L191-L215

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PhiSpec
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {G : X' ⟶ X} {K : Type} [Fintype K]

theorem GlobalTheory.PhiSpec.gs_of_charts {w : LB.Iso L' (L.pull G)} (hw : PGen w) {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}
    {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ G = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L' φ' ε))
    (r : Z ⟶ Y') (z : Z) {p p' : K → L.ι} {q q' : K → L'.ι}
    (hp : ∀ k, G (φ' k (r z)) ∈ L.U (p k)) (hq : ∀ k, φ' k (r z) ∈ L'.U (q k))
    (hp' : ∀ k, G (φ' k (r z)) ∈ L.U (p' k)) (hq' : ∀ k, φ' k (r z) ∈ L'.U (q' k))
    (H : gs (r ≫ h) z (LB.wchart L φ p') (s.f p') =
      (∏ k, gw w (r ≫ φ' k) z (p' k) (q' k) ^ ε k).val * gs r z (LB.wchart L' φ' q') (s'.f q')) :
    gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
      (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k).val * gs r z (LB.wchart L' φ' q) (s'.f q) := by sorry
