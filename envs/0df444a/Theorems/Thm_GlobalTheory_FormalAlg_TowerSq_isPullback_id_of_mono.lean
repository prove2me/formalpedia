-- Prove2me | Theorems.Thm_GlobalTheory_FormalAlg_TowerSq_isPullback_id_of_mono
-- name    : GlobalTheory.FormalAlg.TowerSq.isPullback_id_of_mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:34:09.428917+00:00
-- url     : https://prove2.me/theorems/804f6bc3-f54b-4d30-9e4f-fedaf0502798
-- title:
--   Tower Sq: is Pullback id of mono
-- statement:
--   The Tower Sq construction uses the is Pullback id of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TowerSquares.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TowerSquares.lean#L13-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TowerSquares
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FormalAlg GlobalTheory.FormalAlg.TowerSq

theorem GlobalTheory.FormalAlg.TowerSq.isPullback_id_of_mono {C : Type*} [Category C] {X Y Z : C} (h : X ⟶ Y) (f : Y ⟶ Z) [Mono f] :
    IsPullback h (𝟙 X) f (h ≫ f) := by sorry
