-- Prove2me | Theorems.Thm_GlobalTheory_CosetEuler_mem_offSet_mk
-- name    : GlobalTheory.CosetEuler.mem_offSet_mk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:31.83519+00:00
-- url     : https://prove2.me/theorems/5303b32f-cbed-4d06-973e-cffa99c270da
-- title:
--   Coset Euler: mem off Set mk
-- statement:
--   The Coset Euler construction uses the mem off Set mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L45-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CosetEuler
variable {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)]

theorem GlobalTheory.CosetEuler.mem_offSet_mk {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hJH : J ≤ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) (T : Finset ι) (g : H) :
    (g : H ⧸ J.subgroupOf H) ∈ offSet p K J H T ↔ ∀ v ∉ T, p v g ∈ K v := by sorry
