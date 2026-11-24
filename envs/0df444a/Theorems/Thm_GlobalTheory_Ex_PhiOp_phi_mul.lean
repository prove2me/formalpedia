-- Prove2me | Theorems.Thm_GlobalTheory_Ex_PhiOp_phi_mul
-- name    : GlobalTheory.Ex.PhiOp.phi_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:05:52.918125+00:00
-- url     : https://prove2.me/theorems/93524f59-909b-4dce-afac-2d39d4e9823b
-- title:
--   Phi Op: phi mul
-- statement:
--   The Phi Op construction uses the phi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FeOfPhiTriv.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FeOfPhiTriv.lean#L97-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv
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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.PhiOp
variable {O : Type} [CommRing O] (N : NumD O)

theorem GlobalTheory.Ex.PhiOp.phi_mul {k : ℕ} (p : N.QT k) (u w : Oˣ) (s : N.X → N.A → O) :
    N.phi p (u * w) s = (u : O) • N.phi p w s := by sorry
