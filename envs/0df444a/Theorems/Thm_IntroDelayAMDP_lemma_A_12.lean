-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_12
-- name    : IntroDelayAMDP.lemma_A_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:45:33.574252+00:00
-- url     : https://prove2.me/theorems/7a011bc1-5ec6-45d8-a65f-152952cddfc2
-- title:
--   Lemma A.12 — exploration bonuses, per-episode version
-- statement:
--   Let $P$ be a valid transition, $\pi_k,\pi^\star$ policies, $b$ a function on states and $B$ a function on pairs. If $B(s,a)\ge b(s)+\sum_{s'}P(s'\mid s,a)\sum_{a'}\pi_k(a'\mid s')B(s',a')$ for all pairs, then
--   $$\sum_sq^\star(s)\sum_a(\pi_k(a\mid s)-\pi^\star(a\mid s))B(s,a)\le\sum_a\pi_k(a\mid s_0)B(s_0,a)-\sum_sq^\star(s)b(s).$$
--   If equality holds for all pairs, then $\sum_a\pi_k(a\mid s_0)B(s_0,a)=\sum_sq^{\pi_k}(s)b(s)$.
--
--   The bonus Q-functions thus cancel the bonuses collected by $\pi^\star$ and leave those collected by $\pi_k$.
--
--   Differences from the source:
--   - generalization: b_k the bonus of the algorithm, nonnegative → any real-valued b; reason: the proof does not use the sign of b; the paper's case is a special case
--   - encoding: terminal layer S_H → no terminal layer: last-layer rows vanish and V, B are 0 beyond the last layer; reason: the paper merges S_H into one state, which affects neither q_k nor B_k (p.30)
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.12, p.41; Eq. (3), p.5

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_IsPolicy
import Definitions.Def_IntroDelayAMDP_occS

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma A.12 (Exploration Bonuses; Per-Episode Version)** (printed p.41, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "Fix an episode `k`,
and suppose that `B_k = 0` on `S_H` and `B_k` satisfies Eq. (3) with “=” replaced by “≥”. Then
`∑_{s∈S} q⋆(s) ∑_{a∈A} (π_k(a | s) − π⋆(a | s))B_k(s, a) ≤ ∑_{a∈A} π_k(a | s₀)B_k(s₀, a) − ∑_{s∈S} q⋆(s)b_k(s)`, (43)
where `∑_a π_k(a | s₀)B_k(s₀, a) = ∑_s q^{π_k}(s)b_k(s)` if `B_k` satisfies Eq. (3) with “=”."

For a valid `P`, policies `π_k`, `π⋆`, any `b : S → ℝ` and any `B : S × A → ℝ`: if
`B(s, a) ≥ b(s) + ∑_{s′} P(s′ | s, a) ∑_{a′} π_k(a′ | s′)B(s′, a′)` for all `(s, a)` then (43); if equality holds
for all `(s, a)`, then `∑_a π_k(a | s₀)B(s₀, a) = ∑_s q^{π_k}(s)b(s)`.

**Formalization Note.** The successor sum is empty at the last layer (the row of `P` vanishes), which is
`B_k = 0` on `S_H`. The paper's `b_k ≥ 0` is not needed. -/
theorem lemma_A_12 {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] {H : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (hP : IsTransition L P)
    (πk πstar : St → A → ℝ) (hπk : IsPolicy πk) (hπstar : IsPolicy πstar)
    (b : St → ℝ) (B : St → A → ℝ) :
    ((∀ s a, b s + ∑ s', P s a s' * ∑ a', πk s' a' * B s' a' ≤ B s a) →
      ∑ s, occS L P πstar s * ∑ a, (πk s a - πstar s a) * B s a ≤
        ∑ a, πk L.s0 a * B L.s0 a - ∑ s, occS L P πstar s * b s) ∧
    ((∀ s a, B s a = b s + ∑ s', P s a s' * ∑ a', πk s' a' * B s' a') →
      ∑ a, πk L.s0 a * B L.s0 a = ∑ s, occS L P πk s * b s) := by sorry

end IntroDelayAMDP
