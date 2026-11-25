-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_KerCut_hom_ext_of_appLE
-- name    : GlobalTheory.ZJ.KerCut.hom_ext_of_appLE
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T18:22:25.018961+00:00
-- url     : https://prove2.me/theorems/eb4accd3-5d6f-4c7b-9a4c-cac6d61cb6a1
-- title:
--   Ker Cut: hom ext of app LE
-- statement:
--   The Ker Cut construction uses the hom ext of app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TorusCutByInvariantRatiosField.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TorusCutByInvariantRatiosField.lean#L15-L32

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

theorem GlobalTheory.ZJ.KerCut.hom_ext_of_appLE {X Y : Scheme.{0}} (V : X.Opens) (hV : IsAffineOpen V) (f g : Y ⟶ X)
    (hf : ⊤ ≤ f ⁻¹ᵁ V) (hg : ⊤ ≤ g ⁻¹ᵁ V) (e : f.appLE V ⊤ hf = g.appLE V ⊤ hg) : f = g := by sorry
