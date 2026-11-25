-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_KerCut_appLE_appLE_apply
-- name    : GlobalTheory.ZJ.KerCut.appLE_appLE_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:30.663797+00:00
-- url     : https://prove2.me/theorems/00d4cf57-137a-4059-b78d-64e8bef8688b
-- title:
--   Ker Cut: app LE app LE apply
-- statement:
--   The Ker Cut construction uses the app LE app LE apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TorusCutByInvariantRatiosField.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TorusCutByInvariantRatiosField.lean#L34-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfTorusBased
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitChartsTorusExtensionOverFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TorusCutByInvariantRatiosField
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
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.KerCut

theorem GlobalTheory.ZJ.KerCut.appLE_appLE_apply {X Y Z : Scheme.{0}} (k : Z ⟶ Y) (q : Y ⟶ X) (V : X.Opens) (W : Y.Opens)
    (h : W ≤ q ⁻¹ᵁ V) (h' : ⊤ ≤ k ⁻¹ᵁ W) (p : Z ⟶ X) (e : k ≫ q = p) (h'' : ⊤ ≤ p ⁻¹ᵁ V) (v : Γ(X, V)) :
    (k.appLE W ⊤ h').hom ((q.appLE V W h).hom v) = (p.appLE V ⊤ h'').hom v := by sorry
