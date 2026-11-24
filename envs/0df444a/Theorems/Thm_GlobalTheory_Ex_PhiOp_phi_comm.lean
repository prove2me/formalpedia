-- Prove2me | Theorems.Thm_GlobalTheory_Ex_PhiOp_phi_comm
-- name    : GlobalTheory.Ex.PhiOp.phi_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:34:59.869202+00:00
-- url     : https://prove2.me/theorems/187f0f84-6426-433b-953d-d07f7535250e
-- title:
--   Phi Op: phi comm
-- statement:
--   The Phi Op construction uses the phi comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FeOfPhiTriv.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FeOfPhiTriv.lean#L103-L107

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

theorem GlobalTheory.Ex.PhiOp.phi_comm {k : ℕ} (p p' : N.QT k) (w w' : Oˣ) (s : N.X → N.A → O) :
    N.phi p w (N.phi p' w' s) = (N.wp p p' : O) • N.phi p' w' (N.phi p w s) := by sorry
