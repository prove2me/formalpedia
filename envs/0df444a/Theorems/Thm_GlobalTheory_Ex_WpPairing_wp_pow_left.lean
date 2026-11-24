-- Prove2me | Theorems.Thm_GlobalTheory_Ex_WpPairing_wp_pow_left
-- name    : GlobalTheory.Ex.WpPairing.wp_pow_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:42:38.469877+00:00
-- url     : https://prove2.me/theorems/eec9ba52-2d36-4913-9885-02520cc4df2d
-- title:
--   Wp Pairing: wp pow left
-- statement:
--   The Wp Pairing construction uses the wp pow left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationWeilPairingProperties.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationWeilPairingProperties.lean#L129-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.WpPairing
variable {O : Type} [CommRing O] (N : NumD O)
open scoped BigOperators
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O)

theorem GlobalTheory.Ex.WpPairing.wp_pow_left {k : ℕ} (p q : N.QT k) (n : ℕ) : N.wp (p ^ n) q = N.wp p q ^ n := by sorry
