-- Prove2me | Theorems.Thm_GlobalTheory_CosetEuler_hasSum_step
-- name    : GlobalTheory.CosetEuler.hasSum_step
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:14.456508+00:00
-- url     : https://prove2.me/theorems/b76c82b5-1876-4772-bc67-fd6a9ffac89c
-- title:
--   Coset Euler: has Sum step
-- statement:
--   The Coset Euler construction uses the has Sum step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L149-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean#L149-L168

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

theorem GlobalTheory.CosetEuler.hasSum_step {E : Type} [NormedField E] (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g)
    (c : E) (T : Finset ι) (v : ι) (hv : v ∉ T)
    (hfib : ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (c * f g))
    {s : E} (hs : HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) s)
    (hsum : Summable ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G))) :
    HasSum ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G)) (c * s) := by sorry
