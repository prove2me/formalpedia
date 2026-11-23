-- Prove2me | Theorems.Thm_GlobalTheory_Ex_WpPairing_tk_mul_left
-- name    : GlobalTheory.Ex.WpPairing.tk_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:09.397817+00:00
-- url     : https://prove2.me/theorems/cc2022ec-341e-4cd1-ab60-c750c0ddda04
-- title:
--   Wp Pairing: tk mul left
-- statement:
--   The Wp Pairing construction uses the tk mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationWeilPairingProperties.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationWeilPairingProperties.lean#L23-L32

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

theorem GlobalTheory.Ex.WpPairing.tk_mul_left {k : ℕ} (p p' p'' : N.QT k) :
    N.tk (p * p') p'' * N.θ p''.1.2.b p.1.2.b p'.1.2.b ^ k = N.tk p p'' * N.tk p' p'' := by sorry
