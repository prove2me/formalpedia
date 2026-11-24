-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_combIn_unique
-- name    : GlobalTheory.SecGlue.combIn_unique
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:49:27.05843+00:00
-- url     : https://prove2.me/theorems/f02fb233-e849-4d22-a62f-84bd2078bf56
-- title:
--   Sec Glue: comb In unique
-- statement:
--   The Sec Glue construction uses the comb In unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationInChartUnique.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationInChartUnique.lean#L21-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue

theorem GlobalTheory.SecGlue.combIn_unique : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V → ∀ (S : Type) [CommRing S] (ι : Type) [Fintype ι]
    (u c c' : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    GlobalTheory.SecGlue.IsCombIn V u c w a → GlobalTheory.SecGlue.IsCombIn V u c' w a → c = c' := by sorry
