-- Prove2me | Theorems.Thm_GlobalTheory_CosetEuler_hasSum_offSet_nonneg
-- name    : GlobalTheory.CosetEuler.hasSum_offSet_nonneg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:52.139697+00:00
-- url     : https://prove2.me/theorems/70637b21-ad7b-4c56-985b-f8bfe782b644
-- title:
--   Coset Euler: has Sum off Set nonneg
-- statement:
--   The Coset Euler construction uses the has Sum off Set nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L218-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L218-L228

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
include hpe hpe' he

theorem GlobalTheory.CosetEuler.hasSum_offSet_nonneg (f : G → ℝ) (hf0 : ∀ g ∈ H, 0 ≤ f g)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (A : ι → ℝ)
    (hA : ∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (A v * f g))
    (T : Finset ι) :
    HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) ((∏ v ∈ T, A v) * f 1) := by sorry
