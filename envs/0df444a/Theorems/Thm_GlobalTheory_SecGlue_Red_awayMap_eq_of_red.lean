-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_awayMap_eq_of_red
-- name    : GlobalTheory.SecGlue.Red.awayMap_eq_of_red
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:49:49.67487+00:00
-- url     : https://prove2.me/theorems/b39c5013-bc48-4b98-818e-3c745f4a6557
-- title:
--   Red: away Map eq of red
-- statement:
--   The Red construction uses the away Map eq of red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L106-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L106-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
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
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red
variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem GlobalTheory.SecGlue.Red.awayMap_eq_of_red (π : R →+* R₀) {Y : Scheme.{0}} (a : R)
    (u v : Sp (Localization.Away a) ⟶ Y)
    (h : spMap (Ideal.Quotient.mk (redI π (Localization.Away a))) ≫ u =
      spMap (Ideal.Quotient.mk (redI π (Localization.Away a))) ≫ v) :
    spMap (Localization.awayMap π a) ≫ u = spMap (Localization.awayMap π a) ≫ v := by sorry
