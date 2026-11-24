-- Prove2me | Theorems.Thm_GlobalTheory_UnfoldSemidirect_mem_map_conj_iff
-- name    : GlobalTheory.UnfoldSemidirect.mem_map_conj_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:24:28.576802+00:00
-- url     : https://prove2.me/theorems/d20d58f6-90af-4495-bde9-4b12b0365e73
-- title:
--   Unfold Semidirect: mem map conj iff
-- statement:
--   The Unfold Semidirect construction uses the mem map conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUnfoldSemidirectProduct.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUnfoldSemidirectProduct.lean#L9-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUnfoldSemidirectProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Subgroup
open GlobalTheory.UnfoldSemidirect

theorem GlobalTheory.UnfoldSemidirect.mem_map_conj_iff {G : Type} [Group G] (K : Subgroup G) (g p : G) :
    p ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * p * g ∈ K := by sorry
