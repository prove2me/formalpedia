-- Prove2me | Theorems.Thm_GlobalTheory_TupleCone_coeff_mem_span_pow
-- name    : GlobalTheory.TupleCone.coeff_mem_span_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:34.183778+00:00
-- url     : https://prove2.me/theorems/c7468152-e362-5c1c-a0fc-6dc7432ea0aa
-- title:
--   Tuple Cone: coeff mem span pow
-- statement:
--   The Tuple Cone construction uses the coeff mem span pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L126-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L126-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}

theorem GlobalTheory.TupleCone.coeff_mem_span_pow {p : L[X]} (hp : p ∈ cone o t) (n : ℕ) :
    p.coeff n ∈ Submodule.span o (Set.range t) ^ n := by sorry
