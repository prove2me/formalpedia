-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_15
-- name    : IntroDelayAMDP.lemma_A_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:58:23.509216+00:00
-- url     : https://prove2.me/theorems/fff7d5bd-68a9-4277-a634-2e2870129b53
-- title:
--   Lemma A.15 — bounding Bonus (corrected: on the coverage event instead of G)
-- statement:
--   For $C$ large enough there is an absolute $c>0$ such that for every comparator policy $\pi^\star$, on the event that $P$ satisfies every constraint of (16) in every episode and the event of Lemma A.14 holds,
--   $$\sum_{k=1}^K\sum_sq^\star(s)b_k(s)+\text{Bonus}\le c\bigl(\eta H^3(\nu+H)\iota SAK+H^4S^2A\beta\iota\bigr).$$
--   This bound is pathwise. The width of the confidence sets only enters the $K$-independent term.
--
--   Differences from the source:
--   - correction: conditional on the good event G of Lemma A.1 → on the smaller coverage event, which has the same probability bound δ/4 by Lemma A.1; reason: the proof goes through Lemma A.13, and the printed form is false because of the drop rule. Take H = 2, one action, P(s₁|s₀) = P(s₂|s₀) = ½, β = 40: let s₀ be followed by s₁ in its first 400 visits and by s₂ in the next 1306. P satisfies the constraints of the first 1705 visits (equality q(s₂) ≤ 5β/400 = ½ at n = 400), and those of 1706 visits are unsatisfiable (q(s₁) ≤ 0.49999). So they are dropped afterwards and P ∈ P_k for all k, while q_k(s₁, a) = q_k(s₂, a) = 0 and b_k = H on the last layer, so the left side grows linearly in K
--   - generalization: π⋆ the optimal policy in hindsight → every fixed comparator policy π⋆; reason: the proof never uses optimality; the optimal policy is one such comparator
--   - reading: = O(·) → ≤ c·(·) with c chosen after C; reason: Theorem A.3 uses the upper bound only; both sides are nonnegative up to the comparator's Bonus
--   - reading: conditional on the events, X → X on every sample point of the intersection; reason: the proof is pathwise on the events
--   - reading: C a large enough universal constant → ∃ C₀, ∀ C ≥ C₀; reason: the strong reading of "large enough" (p.30)
--   - encoding: episodes k = 1, …, K → 0-based episodes k < K; reason: Lean convention; same instances
--   - encoding: terminal layer S_H → no terminal layer: last-layer rows vanish and V, B are 0 beyond the last layer; reason: the paper merges S_H into one state, which affects neither q_k nor B_k (p.30)
--   - encoding: the agent's and the environment's randomness → a run of Algorithm 1 as a function of a uniform random tape; reason: one realization of the protocol; the statement depends only on the joint law of the run
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.15, p.43

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_IsPolicy
import Definitions.Def_IntroDelayAMDP_tabParams
import Definitions.Def_IntroDelayAMDP_Tape
import Definitions.Def_IntroDelayAMDP_coverEvent
import Definitions.Def_IntroDelayAMDP_eventA14
import Definitions.Def_IntroDelayAMDP_bonusTerm
import Definitions.Def_IntroDelayAMDP_alg1Bonus
import Definitions.Def_IntroDelayAMDP_occS

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma A.15 (Bounding Bonus)** (printed p.43, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "Conditional on the good event `G` of Lemma A.1
and the event of Lemma A.14, we have `∑_{k=1}^K ∑_{s∈S} q⋆(s)b_k(s) + Bonus = O(ηH³(ν + H)ιSAK + H⁴S²Aβι)`."

For `C` large enough there is an absolute `c > 0` such that, for Algorithm 1 with
`tabParams C 0 S A H K δ` and every comparator policy `π⋆`, on every sample point of
`coverEvent … (K − 1) ∩ eventA14`,
`∑_k ∑_s q⋆(s)b_k(s) + Bonus ≤ c(ηH³(ν + H)ιSAK + H⁴S²Aβι)`.

**Formalization Note.** "`= O(·)`" is read as the upper bound with an absolute constant chosen after
`C`; the bound is pathwise on the two events.

**Correction.** The good event `G` is replaced by the smaller `coverEvent` (with the same probability
bound `δ/4`, Lemma A.1), because the proof goes through Lemma A.13. On `G` itself the bound fails: with
`H = 2`, one action and `P(s₁ | s₀) = P(s₂ | s₀) = ½`, take `β = 40`, and let `s₀` be followed by `s₁` in
its first `400` visits and by `s₂` in the next `1306`. `P` satisfies the constraints of the first `1705`
visits, and those of `1706` visits are unsatisfiable (`q(s₂) ≤ 5β/400 = ½` against an upper bound `0.49999`
on `q(s₁)`). So they are dropped from then on and `P ∈ P_k` for all `k`, while `q_k(s₁, a) = q_k(s₂, a) = 0`
and `b_k = H` on the last layer in all later episodes, which makes the left side linear in `K`. -/
theorem lemma_A_15 :
    ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ c > (0 : ℝ),
      ∀ (St A : Type) [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] (H K : ℕ)
      (L : LayeredSpace St H) (P : St → A → St → ℝ), IsTransition L P →
      ∀ ℓ : ℕ → St → A → ℝ, (∀ k < K, ∀ s a, 0 ≤ ℓ k s a ∧ ℓ k s a ≤ 1) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → 1 ≤ K →
      ∀ πstar : St → A → ℝ, IsPolicy πstar →
      let p := tabParams C 0 (Fintype.card St) (Fintype.card A) H K δ
      ∀ ω ∈ coverEvent K L P ℓ p (K - 1) ∩ eventA14 K L P ℓ p,
        ∑ k ∈ Finset.range K, ∑ s, occS L P πstar s * alg1Bonus L P ℓ p ω k s +
            bonusTerm L P ℓ p ω πstar ≤
          c * (p.eta * (H : ℝ) ^ 3 * (p.nu + H) * p.iota * (Fintype.card St : ℝ) *
              (Fintype.card A : ℝ) * K +
            (H : ℝ) ^ 4 * (Fintype.card St : ℝ) ^ 2 * (Fintype.card A : ℝ) * p.beta * p.iota) := by sorry

end IntroDelayAMDP
