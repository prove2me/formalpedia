-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_isRed_self
-- name    : GlobalTheory.SecGlue.Red.isRed_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:49:04.046291+00:00
-- url     : https://prove2.me/theorems/ea4c6802-f7bc-4ce7-99c4-d9339ea32363
-- title:
--   Red: is Red self
-- statement:
--   The Red construction uses the is Red self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L77-L83

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

theorem GlobalTheory.SecGlue.Red.isRed_self (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) (a : R) (u : Sp (Localization.Away a) ⟶ Y)
    (hu : spMap (Localization.awayMap π a) ≫ u =
      spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀) :
    IsRed π hπ g₀ (Localization.Away a) u := by sorry
