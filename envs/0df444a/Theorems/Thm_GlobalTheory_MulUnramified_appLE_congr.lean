-- Prove2me | Theorems.Thm_GlobalTheory_MulUnramified_appLE_congr
-- name    : GlobalTheory.MulUnramified.appLE_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:15.021983+00:00
-- url     : https://prove2.me/theorems/5f1cef82-825b-4dad-8a0c-1ac6130c3590
-- title:
--   Mul Unramified: app LE congr
-- statement:
--   The Mul Unramified construction uses the app LE congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L20-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulUnramified

theorem GlobalTheory.MulUnramified.appLE_congr {T X : Scheme.{0}} {f g : T ⟶ X} (h : f = g) (V : X.Opens) (W : T.Opens)
    (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) : f.appLE V W hf = g.appLE V W hg := by sorry
