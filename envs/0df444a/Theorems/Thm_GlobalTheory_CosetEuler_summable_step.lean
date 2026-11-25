-- Prove2me | Theorems.Thm_GlobalTheory_CosetEuler_summable_step
-- name    : GlobalTheory.CosetEuler.summable_step
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:49:09.870635+00:00
-- url     : https://prove2.me/theorems/f243c708-9952-4c34-a621-c79b1b840c77
-- title:
--   Coset Euler: summable step
-- statement:
--   The Coset Euler construction uses the summable step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L170-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L170-L190

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

theorem GlobalTheory.CosetEuler.summable_step (f : G → ℝ) (hf0 : ∀ g ∈ H, 0 ≤ f g)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g)
    (c : ℝ) (T : Finset ι) (v : ι) (hv : v ∉ T)
    (hfib : ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (c * f g))
    {s : ℝ} (hs : HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) s) :
    Summable ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G)) := by sorry
