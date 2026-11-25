-- Prove2me | Theorems.Thm_GlobalTheory_CosetEuler_mem_range_stepMap
-- name    : GlobalTheory.CosetEuler.mem_range_stepMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:58.865607+00:00
-- url     : https://prove2.me/theorems/387fd6fb-ed79-4cdf-9353-cbedf9269cc4
-- title:
--   Coset Euler: mem range step Map
-- statement:
--   The Coset Euler construction uses the mem range step Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L113-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L113-L135

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
variable [DecidableEq ι] {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hJH : J ≤ H) (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
include hJH hpe hpe' he hJ

theorem GlobalTheory.CosetEuler.mem_range_stepMap (T : Finset ι) (v : ι) (y : H ⧸ J.subgroupOf H)
    (hy : y ∈ offSet p K J H (insert v T)) : y ∈ Set.range (stepMap e p K J H he T v) := by sorry
