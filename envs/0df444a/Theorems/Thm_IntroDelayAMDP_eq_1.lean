-- Prove2me | Theorems.Thm_IntroDelayAMDP_eq_1
-- name    : IntroDelayAMDP.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:03.07766+00:00
-- url     : https://prove2.me/theorems/c9283c9d-5cb2-4306-8aee-a39057bc7cf7
-- title:
--   Eq. (1) — performance difference
-- statement:
--   Let $P$ be a valid transition, $\ell_k$ any losses, $\pi_k$ any per-episode policies and $\pi^\star$ any comparator, with $q^\star=q^{\pi^\star}$. Then
--   $$R_K=\sum_{s}q^\star(s)\sum_{k}\sum_{a}\bigl(\pi_k(a\mid s)-\pi^\star(a\mid s)\bigr)Q^{\pi_k}_k(s,a).$$
--   This decomposes the regret into a weighted sum of per-state bandit regrets with losses $Q^{\pi_k}_k$, and is the base of the decomposition (28).
--
--   Differences from the source:
--   - generalization: π_k the agent's policies and π⋆ the optimal policy in hindsight → arbitrary real-valued π_k, π⋆ and arbitrary real losses; reason: the telescoping uses only the Bellman recursions and the layering; the paper's case is a special case
--   - encoding: episodes k = 1, …, K → 0-based episodes k < K; reason: Lean convention; same instances
--   - encoding: terminal layer S_H → no terminal layer: last-layer rows vanish and V, B are 0 beyond the last layer; reason: the paper merges S_H into one state, which affects neither q_k nor B_k (p.30)
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (1), p.4

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_regret
import Definitions.Def_IntroDelayAMDP_qFun
import Definitions.Def_IntroDelayAMDP_occS

namespace IntroDelayAMDP

open MeasureTheory

/-- **Eq. (1): performance difference** (printed p.4, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "`R_K = ∑_{s∈S} q⋆(s) ∑_{k=1}^K
∑_{a∈A} (π_k(a | s) − π⋆(a | s)) Q^{π_k}_k(s, a)`".

For a layered space, a valid transition `P`, any losses `ℓ`, any per-episode policies `π_k` and any
comparator `π⋆` with `q⋆ = q^{π⋆}`, the regret over the 0-based episodes `k < K` equals the
weighted sum of per-state bandit regrets with losses `Q^{π_k}_k`.

**Formalization Note.** Deterministic identity; it holds for arbitrary real-valued `π_k`, `π⋆` and `ℓ`
(the telescoping uses only the Bellman recursions and the layering). -/
theorem eq_1 {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] {H : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (hP : IsTransition L P)
    (ℓ : ℕ → St → A → ℝ) (πs : ℕ → St → A → ℝ) (πstar : St → A → ℝ) (K : ℕ) :
    regret L P ℓ πs πstar K =
      ∑ s, occS L P πstar s * ∑ k ∈ Finset.range K, ∑ a,
        (πs k s a - πstar s a) * qFun L P (ℓ k) (πs k) s a := by sorry

end IntroDelayAMDP
