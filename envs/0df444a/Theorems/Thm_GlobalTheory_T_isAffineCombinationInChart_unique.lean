-- Prove2me | Theorems.Thm_GlobalTheory_T_isAffineCombinationInChart_unique
-- name    : GlobalTheory.T.isAffineCombinationInChart_unique
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:27.22631+00:00
-- url     : https://prove2.me/theorems/35d4262a-d3d8-4e30-8392-9758ad66e44f
-- title:
--   T: is Affine Combination In Chart unique
-- statement:
--   The T construction uses the is Affine Combination In Chart unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationInChartUniqueStatement.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationInChartUniqueStatement.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUnique
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUniqueStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isAffineCombinationInChart_unique : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V → ∀ (S : Type) [CommRing S] (ι : Type) [Fintype ι]
    (u c c' : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    GlobalTheory.SecGlue.IsCombIn V u c w a → GlobalTheory.SecGlue.IsCombIn V u c' w a → c = c' := by sorry
