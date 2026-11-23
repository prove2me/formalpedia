-- Prove2me | Theorems.Thm_GlobalTheory_Ex_WpPairing_wp_mul_right
-- name    : GlobalTheory.Ex.WpPairing.wp_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:35.330599+00:00
-- url     : https://prove2.me/theorems/cf58a1cf-457f-4e92-af85-65f0a6a46fac
-- title:
--   Wp Pairing: wp mul right
-- statement:
--   The Wp Pairing construction uses the wp mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationWeilPairingProperties.lean#L120-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationWeilPairingProperties.lean#L120-L121

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

theorem GlobalTheory.Ex.WpPairing.wp_mul_right {k : ℕ} (p p' p'' : N.QT k) : N.wp p (p' * p'') = N.wp p p' * N.wp p p'' := by sorry
