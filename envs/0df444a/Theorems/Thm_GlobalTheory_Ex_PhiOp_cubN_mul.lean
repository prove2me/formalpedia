-- Prove2me | Theorems.Thm_GlobalTheory_Ex_PhiOp_cubN_mul
-- name    : GlobalTheory.Ex.PhiOp.cubN_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:06:12.67296+00:00
-- url     : https://prove2.me/theorems/75b249c0-e59b-49b5-9d55-5a67dad1b4a6
-- title:
--   Phi Op: cub N mul
-- statement:
--   The Phi Op construction uses the cub N mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FeOfPhiTriv.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FeOfPhiTriv.lean#L26-L38

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
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem GlobalTheory.Ex.PhiOp.cubN_mul (k : ℕ) (b b' x : A) :
    cubN θ k 1 (b * b') x * θ b b' x ^ k = θ (b ^ k) (b' ^ k) x * cubN θ k 1 b x * cubN θ k 1 b' x := by sorry
