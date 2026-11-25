-- Prove2me | Theorems.Thm_GlobalTheory_UU_RelModel_gs_scal
-- name    : GlobalTheory.UU.RelModel.gs_scal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:05:14.820796+00:00
-- url     : https://prove2.me/theorems/cb1f0eaf-7028-41e0-a4af-34a6682e3d7c
-- title:
--   Rel Model: gs scal
-- statement:
--   The Rel Model construction uses the gs scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueSamePtRight.lean#L331-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueSamePtRight.lean#L331-L334

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
open GlobalTheory.UnifZero GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate

theorem GlobalTheory.UU.RelModel.gs_scal {Y Z : Scheme.{0}} {B : Type} [CommRing B] (p : Y ⟶ Spec (CommRingCat.of B)) (a : B)
    (r : Z ⟶ Y) (z : Z) : gs r z ⊤ (scal p a) = gs (𝟙 Z) z ⊤ (scal (r ≫ p) a) := by sorry
