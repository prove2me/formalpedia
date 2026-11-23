-- Prove2me | Theorems.Thm_GlobalTheory_Ex_WpPairing_s_nsmul
-- name    : GlobalTheory.Ex.WpPairing.s_nsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:04.210361+00:00
-- url     : https://prove2.me/theorems/269d2564-afd6-4dc9-8e2d-b6ac0e4f77e1
-- title:
--   Wp Pairing: s nsmul
-- statement:
--   The Wp Pairing construction uses the s nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationWeilPairingProperties.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationWeilPairingProperties.lean#L13-L21

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

theorem GlobalTheory.Ex.WpPairing.s_nsmul (g : N.Gt) (n : ℕ) (y : N.X) : g.s (n • y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ n 1 (N.c y) g.b = g.s y ^ n := by sorry
