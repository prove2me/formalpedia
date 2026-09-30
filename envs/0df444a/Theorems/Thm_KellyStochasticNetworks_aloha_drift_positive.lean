-- Prove2me | Theorems.Thm_KellyStochasticNetworks_aloha_drift_positive
-- name    : KellyStochasticNetworks.aloha_drift_positive
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:10:41.159581+00:00
-- url     : https://prove2.me/theorems/2a54926a-1528-442c-b461-07004c9858d8
-- title:
--   Section 5.1 — the ALOHA backlog drifts upward once it is large
-- statement:
--   In the ALOHA protocol with arrival rate $\nu > 0$ and retransmission probability
--   $f \in (0,1)$, the backlog $N_t$ of packets awaiting retransmission is a Markov chain with
--   drift
--   $$\mathbb{E}[N_{t+1}-N_t \mid N_t=n] = \nu - \mathbb{P}(Z_t = 1 \mid N_t = n),$$
--   where $\mathbb{P}(Z_t = 1 \mid N_t = n) = e^{-\nu}nf(1-f)^{n-1} + \nu e^{-\nu}(1-f)^{n}$ is the
--   probability that exactly one transmission is attempted. Three facts.
--
--   1. For $n \ge 1$ that probability factors as
--      $$e^{-\nu}\bigl(nf+(1-f)\nu\bigr)(1-f)^{n-1},$$
--      which is the form in which the book states the drift condition.
--   2. It tends to $0$ as $n \to \infty$, for any fixed $f \in (0,1)$.
--   3. Consequently, for every $\nu > 0$ there is a backlog beyond which the drift is strictly
--      positive: the success probability is eventually smaller than $\nu$.
--
--   The reading is the one the book draws: whatever the arrival rate, once the backlog is large
--   enough ALOHA's collisions make it grow larger still. Note what this does *not* establish —
--   positive drift does not imply transience, as Remark 5.2 shows with an explicit recurrent chain
--   of positive drift. The stronger conclusion, that ALOHA jams forever, is Proposition 5.3.
--
--   **Formalization Note** The success probability is the closed form of the definition item; the
--   Poisson-plus-binomial derivation of it is not part of this statement. The factorization is
--   asserted only for $n \ge 1$, where $(1-f)^{n-1}$ means what it should.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 110 (PDF p. 118), section 5.1: 'P(Z_t = 1 | N_t = n) = e^{-nu} . n f (1-f)^{n-1} + nu e^{-nu} . (1-f)^n. We conclude that the drift is positive (i.e., backlog is on average growing) if nu > e^{-nu}(nf + (1-f)nu)(1-f)^{n-1}. For any fixed retransmission probability f, the quantity on the right-hand side tends to 0 as n -> infinity. Consequently, for any positive arrival rate of messages nu, if the backlog is large enough, we expect it to grow even larger.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem aloha_drift_positive (ν f : ℝ) (hν : 0 < ν) (hf : 0 < f) (hf1 : f < 1) :
    (∀ n : ℕ, 1 ≤ n → alohaSuccessProb ν f n
        = Real.exp (-ν) * ((n : ℝ) * f + (1 - f) * ν) * (1 - f) ^ (n - 1))
      ∧ Filter.Tendsto (fun n : ℕ => alohaSuccessProb ν f n) Filter.atTop (nhds 0)
      ∧ ∃ N : ℕ, ∀ n ≥ N, alohaSuccessProb ν f n < ν := by sorry

end KellyStochasticNetworks
