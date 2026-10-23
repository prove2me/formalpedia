-- Prove2me | Theorems.Thm_GoTBandit_Main_lemma_V_3
-- name    : GoTBandit.Main.lemma_V_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:15.342989+00:00
-- url     : https://prove2.me/theorems/7e8f67cd-d0d3-4b8c-b1ae-06b01ccd38b8
-- title:
--   Lemma V.3, p. 9 — the estimated assignment problem of an epoch has a unique optimum almost surely
-- statement:
--   Consider $N\le M$ players running Algorithm 1 with i.i.d. rewards as in Definition II.1, $c_1\ge1$, $\delta>0$, and let $\mu^k_{n,i}$ be the estimates after the exploration phase of epoch $k\ge1$, with $V_{n,i}$ the number of collision-free exploration visits of player $n$ to arm $i$ so far. Then, almost surely on the event that every $V_{n,i}\ge1$ and every $\mu^k_{n,i}>0$, the problem
--
--   $$
--   \max_a\sum_{n=1}^Nu_n(a),\qquad u_n(a)=\mu^k_{n,a_n}\eta_{a_n}(a),
--   $$
--
--   has a unique optimal solution. Formally,
--
--   $$
--   \mathbb P\big(\forall n,i:\ V_{n,i}\ge1,\ \mu^k_{n,i}>0,\ \text{and the optimum is not unique}\big)=0.
--   $$
--
--   Uniqueness of the optimal state is what lets the players agree on a single assignment without communication.
--
--   **Formalization Note** The lemma is stated on the event of visited arms and positive estimates. As printed it fails in early epochs: an arm with no collision-free visit has the undefined estimate $0/0$, and with estimates $\le0$ (Gaussian rewards satisfy Definition II.1) a collision profile of value $0$ can tie with another profile. The proof's first step ("an optimal solution must not have any collisions") presupposes positive estimates. On the success event of Lemma IV.3 every estimate is positive when $N\ge2$.
-- source:
--   Bistritz and Leshem, Game of Thrones: Fully Distributed Learning for Multiplayer Bandits, arXiv:1810.11162v7, p. 9, Lemma V.3

import Mathlib
import Definitions.Def_GoTBandit_Main_Algorithm

open Finset MeasureTheory ProbabilityTheory

namespace GoTBandit.Main

/-- Lemma V.3, p. 9: almost surely, the assignment problem with the estimated means
`μ^k_{n,i}` of epoch `k` has a unique optimal solution. Disclosed restriction: on the event
that every arm has a collision-free exploration visit and every estimate is positive. -/
theorem lemma_V_3 {N M : ℕ} (hNM : N ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin N → Fin M → ℕ → Ω → ℝ) (μ σ2 b : Fin N → Fin M → ℝ)
    (hr : IIDRewards P r μ σ2 b) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (hξ : Seeds P r ξ)
    (p : GoTParams) (hc1 : 0 < p.c1) (hδ : 0 < p.δ) (k : ℕ) (hk : 1 ≤ k) :
    P {ω | (∀ n i, 1 ≤ visitCount p hNM r ξ k n i ω ∧ 0 < est p hNM r ξ k n i ω) ∧
        ¬ ∃! a, IsOptimal (fun n i => est p hNM r ξ k n i ω) a} = 0 := by sorry

end GoTBandit.Main
