-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_CombEx_top_of_comp
-- name    : GlobalTheory.SecGlue.CombEx.top_of_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:52:55.71721+00:00
-- url     : https://prove2.me/theorems/0c90b3ac-92ef-4b27-9eb6-533872484c3e
-- title:
--   Comb Ex: top of comp
-- statement:
--   The Comb Ex construction uses the top of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineCombinationSquareZeroLiftsChart.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineCombinationSquareZeroLiftsChart.lean#L18-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.CombEx

theorem GlobalTheory.SecGlue.CombEx.top_of_comp {A B Y : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ Y) (V : Y.Opens) (h : g ⁻¹ᵁ V = ⊤) :
    (f ≫ g) ⁻¹ᵁ V = ⊤ := by sorry
