-- Prove2me | Theorems.Thm_GlobalTheory_Ex_WpPairing_wp_congr_left
-- name    : GlobalTheory.Ex.WpPairing.wp_congr_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:42:44.852721+00:00
-- url     : https://prove2.me/theorems/b0560881-881a-4d0b-b194-9d837f3b579b
-- title:
--   Wp Pairing: wp congr left
-- statement:
--   The Wp Pairing construction uses the wp congr left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationWeilPairingProperties.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationWeilPairingProperties.lean#L150-L152

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

theorem GlobalTheory.Ex.WpPairing.wp_congr_left {k : ℕ} {p p' : N.QT k} (h : N.QEq p p') (q : N.QT k) : N.wp p q = N.wp p' q := by sorry
