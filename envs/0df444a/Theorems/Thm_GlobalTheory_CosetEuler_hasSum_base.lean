-- Prove2me | Theorems.Thm_GlobalTheory_CosetEuler_hasSum_base
-- name    : GlobalTheory.CosetEuler.hasSum_base
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:13.101176+00:00
-- url     : https://prove2.me/theorems/4cc6f025-06ad-45c1-9867-3257745192c9
-- title:
--   Coset Euler: has Sum base
-- statement:
--   The Coset Euler construction uses the has Sum base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L205-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L205-L214

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
variable [DecidableEq ι] {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)}
    {J H : Subgroup G}
    (hJH : J ≤ H) (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
include hJH hJ

theorem GlobalTheory.CosetEuler.hasSum_base {E : Type} [AddCommMonoid E] [TopologicalSpace E] (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) :
    HasSum ((offSet p K J H ∅).indicator fun y => f ((y.out : H) : G)) (f 1) := by sorry
