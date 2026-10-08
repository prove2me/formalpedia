-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_4_2
-- name    : MartingaleHT.InfiniteServer.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:55.971231+00:00
-- url     : https://prove2.me/theorems/97432aa3-b6be-4f70-ade2-d5a91705654e
-- title:
--   Lemma 4.2 — desired fluid limit $\Phi_{S,n}=\frac{\mu}{n}\int_0^\cdot Q_n\Rightarrow\mu e$ in $D$
-- statement:
--   Fix $\mu>0$. For every $n\ge1$ let $Q_n$ be the number of customers in an $M/M/\infty$ queue with arrival rate $\lambda_n=n\mu$ and service rate $\mu$ per customer, built as in (12) from its own pair of independent unit-rate Poisson processes $A_n,S_n$ and an initial number $Q_n(0)$ independent of them, all systems on one probability space $(\Omega,\mathcal F,P)$. Let $X_n(t)=(Q_n(t)-n)/\sqrt n$, and assume $X_n(0)\Rightarrow X(0)$ in $\mathbb R$, i.e. $X_n(0)$ converges in distribution to a probability law $\nu$ on $\mathbb R$ (4).
--   Then the fluid-scaled cumulative service intensity $\Phi_{S,n}(t)=\frac{\mu}{n}\int_0^tQ_n(s)\,ds$ (67) satisfies
--   $$
--   \Phi_{S,n}\Rightarrow\mu e\quad\text{in }D\text{ as }n\to\infty, \tag{68}
--   $$
--   where $e(t)=t$; that is, for every $T\ge0$ and $\varepsilon>0$, $P\big(\sup_{0\le t\le T}|\Phi_{S,n}(t)-\mu t|\ge\varepsilon\big)\to0$.
--
--   This is the random time change in $M_{n,2}=M_{S,n}\circ\Phi_{S,n}$, whose convergence is needed for the composition argument of Lemma 4.4.
--
--   **Formalization Note** Convergence in distribution to a deterministic continuous limit is stated as uniform convergence on compact intervals in probability (p. 229). The systems use one pair of Poisson processes per $n$ (the paper uses one pair for all $n$, a special case; weak convergence depends only on laws). The hypothesis (4) is stated with bounded continuous test functions. No moment condition on $Q_n(0)$ is assumed: §6.3 of the paper removes it.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 229, Lemma 4.2, (67)–(68)

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

/-- **Lemma 4.2** (desired fluid limit, p. 229). Under the conditions of Theorem 1.1,
`Φ_{S,n}(t) = (μ/n) ∫₀ᵗ Qₙ(s) ds` converges to the path `t ↦ μt` uniformly on compact time
intervals in probability (convergence in distribution in `D` to a deterministic continuous
limit). -/
theorem lemma_4_2 (μ : ℝ) (hμ : 0 < μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsMMInfSystem P (n * μ) μ (A n) (S n) (Q n))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (scaled n (Q n) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) :
    UocInProb P (fun n ω t (_ : Fin 1) => phiS n μ (Q n) ω t) (fun t _ => μ * t) := by sorry

end MartingaleHT.InfiniteServer
