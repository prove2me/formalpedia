-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_lemma_4_3
-- name    : MartingaleHT.InfiniteServer.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:05.547414+00:00
-- url     : https://prove2.me/theorems/7890a317-9aa1-45bd-9aed-5e5857460ea5
-- title:
--   Lemma 4.3 — basic fluid limit $\Psi_{S,n}=Q_n/n\Rightarrow\omega\equiv1$ in $D$
-- statement:
--   Fix $\mu>0$. For every $n\ge1$ let $Q_n$ be the number of customers in an $M/M/\infty$ queue with arrival rate $\lambda_n=n\mu$ and service rate $\mu$ per customer, built as in (12) from its own pair of independent unit-rate Poisson processes $A_n,S_n$ and an initial number $Q_n(0)$ independent of them, all systems on one probability space $(\Omega,\mathcal F,P)$. Let $X_n(t)=(Q_n(t)-n)/\sqrt n$, and assume $X_n(0)\Rightarrow X(0)$ in $\mathbb R$, i.e. $X_n(0)$ converges in distribution to a probability law $\nu$ on $\mathbb R$ (4).
--   Then the fluid-scaled number in system $\Psi_{S,n}(t)=Q_n(t)/n$ (69) satisfies
--   $$
--   \Psi_{S,n}\Rightarrow\omega\quad\text{in }D\text{ as }n\to\infty, \tag{70}
--   $$
--   where $\omega(t)=1$ for $t\ge0$; that is, for every $T\ge0$ and $\varepsilon>0$, $P\big(\sup_{0\le t\le T}|Q_n(t)/n-1|\ge\varepsilon\big)\to0$.
--
--   The fluid limit is the input of Lemma 4.4, which completes the proof of Theorem 1.1.
--
--   **Formalization Note** Convergence in distribution to a deterministic continuous limit is convergence in probability (p. 229); it is stated as uniform convergence on compact intervals in probability. The paper's $\omega$ is the constant path $1$, not a sample point. The systems use one pair of Poisson processes per $n$ (the paper uses one pair for all $n$, a special case; weak convergence depends only on laws). The hypothesis (4) is stated with bounded continuous test functions. No moment condition on $Q_n(0)$ is assumed: §6.3 of the paper removes it.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 229, Lemma 4.3, (69)–(70)

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

/-- **Lemma 4.3** (basic fluid limit, p. 229). Under the conditions of Theorem 1.1,
`Ψ_{S,n}(t) = Qₙ(t)/n` converges to the constant path `1` uniformly on compact time intervals
in probability (convergence in distribution in `D` to a deterministic continuous limit). -/
theorem lemma_4_3 (μ : ℝ) (hμ : 0 < μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsMMInfSystem P (n * μ) μ (A n) (S n) (Q n))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (scaled n (Q n) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) :
    UocInProb P (fun n ω t (_ : Fin 1) => psiS n (Q n) ω t) (fun _ _ => 1) := by sorry

end MartingaleHT.InfiniteServer
