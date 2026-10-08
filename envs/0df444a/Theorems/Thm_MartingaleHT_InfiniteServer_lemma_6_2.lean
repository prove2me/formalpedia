-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_6_2
-- name    : MartingaleHT.InfiniteServer.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:56.160084+00:00
-- url     : https://prove2.me/theorems/e947d851-b326-487b-9326-3dd5909fccea
-- title:
--   Lemma 6.2 — stochastic boundedness of $\langle M_{n,2}\rangle(t)=\frac{\mu}{n}\int_0^tQ_n(s)\,ds$
-- statement:
--   Fix $\mu>0$. For every $n\ge1$ let $Q_n$ be the number of customers in an $M/M/\infty$ queue with arrival rate $\lambda_n=n\mu$ and service rate $\mu$ per customer, built as in (12) from its own pair of independent unit-rate Poisson processes $A_n,S_n$ and an initial number $Q_n(0)$ independent of them, all systems on one probability space $(\Omega,\mathcal F,P)$. Let $X_n(t)=(Q_n(t)-n)/\sqrt n$, and assume $X_n(0)\Rightarrow X(0)$ in $\mathbb R$, i.e. $X_n(0)$ converges in distribution to a probability law $\nu$ on $\mathbb R$ (4).
--   Assume moreover $E[Q_n(0)]<\infty$ for every $n\ge1$ (the assumption of Theorem 3.4). Then for each $t>0$ the random variables
--   $$
--   \langle M_{n,2}\rangle(t)=\frac{\mu}{n}\int_0^tQ_n(s)\,ds,\qquad n\ge1,
--   $$
--   are stochastically bounded in $\mathbb R$.
--
--   This is the one non-trivial input of the martingale route to the fluid limit; $\langle M_{n,1}\rangle(t)=\mu t$ is deterministic.
--
--   **Formalization Note** The systems use one pair of Poisson processes per $n$ (the paper uses one pair for all $n$, a special case; weak convergence depends only on laws). The hypothesis (4) is stated with bounded continuous test functions.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 240, Lemma 6.2

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_InfiniteServer_Model
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MartingaleHT.InfiniteServer

open BellWilliams2001.ThresholdPolicy ErlangA.Diffusion

/-- **Lemma 6.2** (p. 240). Under the assumptions of Theorems 1.1 and 3.4 (the conditions of
Theorem 1.1 and `E[Qₙ(0)] < ∞` for every `n ≥ 1`), for each `t > 0` the random variables
`⟨M_{n,2}⟩(t) = (μ/n) ∫₀ᵗ Qₙ(s) ds`, `n ≥ 1`, are stochastically bounded in `ℝ`. -/
theorem lemma_6_2 (μ : ℝ) (hμ : 0 < μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsMMInfSystem P (n * μ) μ (A n) (S n) (Q n))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (scaled n (Q n) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ))))
    (hmom : ∀ n : ℕ, 1 ≤ n → Integrable (fun ω => (Q n ω 0 : ℝ)) P) :
    ∀ t : ℝ, 0 < t → IsSBReal P (fun n ω => phiS n μ (Q n) ω t) := by sorry

end MartingaleHT.InfiniteServer
