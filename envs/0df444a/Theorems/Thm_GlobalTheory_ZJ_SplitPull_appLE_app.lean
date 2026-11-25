-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_SplitPull_appLE_app
-- name    : GlobalTheory.ZJ.SplitPull.appLE_app
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:40:38.926918+00:00
-- url     : https://prove2.me/theorems/ec0964f9-c1c4-406e-bb3f-e3b93c9dea65
-- title:
--   Split Pull: app LE app
-- statement:
--   The Split Pull construction uses the app LE app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L79-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPullAndSplitPull
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
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.SplitPull
open GlobalTheory.UU

theorem GlobalTheory.ZJ.SplitPull.appLE_app {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : s = r ≫ φ) (V : C.Opens)
    (k : ⊤ ≤ r ⁻¹ᵁ φ ⁻¹ᵁ V) (k' : ⊤ ≤ s ⁻¹ᵁ V) (u : Γ(C, V)) :
    (r.appLE (φ ⁻¹ᵁ V) ⊤ k).hom ((φ.app V).hom u) = (s.appLE V ⊤ k').hom u := by sorry
