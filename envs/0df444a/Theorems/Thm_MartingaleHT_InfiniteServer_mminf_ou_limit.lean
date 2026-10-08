-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_mminf_ou_limit
-- name    : MartingaleHT.InfiniteServer.mminf_ou_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:22.619141+00:00
-- url     : https://prove2.me/theorems/4dff7011-1fde-45fc-b3a5-ec59a757a24b
-- title:
--   Theorem 1.1 — the centred, $\sqrt n$-scaled $M/M/\infty$ queue with $\lambda_n=n\mu$ converges in $D$ to the Ornstein–Uhlenbeck process $dX=-\mu X\,dt+\sqrt{2\mu}\,dB$
-- statement:
--   Fix $\mu>0$. For every $n\ge1$ let $Q_n$ be the number of customers in an $M/M/\infty$ queue with arrival rate $\lambda_n=n\mu$ and service rate $\mu$ per customer, built as in (12) from its own pair of independent unit-rate Poisson processes $A_n,S_n$ and an initial number $Q_n(0)$ independent of them, all systems on one probability space $(\Omega,\mathcal F,P)$. Let $X_n(t)=(Q_n(t)-n)/\sqrt n$, and assume $X_n(0)\Rightarrow X(0)$ in $\mathbb R$, i.e. $X_n(0)$ converges in distribution to a probability law $\nu$ on $\mathbb R$ (4).
--   Then
--   $$
--   X_n\Rightarrow X\quad\text{in }D\text{ as }n\to\infty,
--   $$
--   where $X$ is the Ornstein–Uhlenbeck process: $B$ is a standard Brownian motion, $X(0)$ has law $\nu$ and is independent of $B$, and
--   $$
--   X(t)=X(0)+\sqrt{2\mu}\,B(t)-\mu\int_0^tX(s)\,ds,\qquad t\ge0 . \tag{5}
--   $$
--   Precisely: (1) such a process $X$ exists on some probability space and $X_n\Rightarrow X$; (2) every such process, on any probability space, is the limit of $X_n$ in the same sense.
--
--   This is the heavy-traffic limit of the infinite-server queue: the number of busy servers fluctuates around $n$ on the scale $\sqrt n$ like a mean-reverting Gaussian diffusion with infinitesimal mean $-\mu x$ and infinitesimal variance $2\mu$.
--
--   **Formalization Note** The limit uses the published Erlang-A diffusion with $\beta=0$, $\theta=\mu$, whose drift is $-\mu x$; a solution includes adaptedness to $\sigma(X(0))\vee\sigma(B(s):s\le t)$. Convergence in $D$ is stated in coupling form (`CouplingConverges`), equivalent to $J_1$ weak convergence for continuous limits; the limit space is in universe `Type`. Clause (2) carries the uniqueness in law of the limit. The SDE form (6) and the infinitesimal-moment description are equivalent descriptions and are not stated separately. The systems use one pair of Poisson processes per $n$ (the paper uses one pair for all $n$, a special case; weak convergence depends only on laws). The hypothesis (4) is stated with bounded continuous test functions. No moment condition on $Q_n(0)$ is assumed: §6.3 of the paper removes it.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 196, Theorem 1.1, (3)–(5); p. 195, (1); p. 241, §6.3

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

/-- **Theorem 1.1** (p. 196). Let `μ > 0` and, for every `n ≥ 1`, let `Qₙ` be the number in
system of an `M/M/∞` queue with arrival rate `λₙ = nμ` and service rate `μ`, built from its own
pair of independent unit-rate Poisson processes `Aₙ, Sₙ` and an initial value `Qₙ(0)` independent
of them, all systems on one probability space. Let `Xₙ(t) = (Qₙ(t) − n)/√n`. If `Xₙ(0)`
converges in distribution to a probability law `ν` on `ℝ`, then:
1. there is an Ornstein–Uhlenbeck process `X`, i.e. a solution of
   `X(t) = X(0) + √(2μ) B(t) − μ ∫₀ᵗ X(s) ds` with `X(0) ∼ ν` independent of the standard
   Brownian motion `B`, and `Xₙ ⇒ X` in `D` (coupling form `CouplingConverges`);
2. every such solution, on any probability space, is a limit of `Xₙ` in the same sense.
The drift `drift μ 0 μ x` of `ErlangA.Diffusion` equals `−μx`. -/
theorem mminf_ou_limit (μ : ℝ) (hμ : 0 < μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsMMInfSystem P (n * μ) μ (A n) (S n) (Q n))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (scaled n (Q n) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (B : ℝ≥0 → Ω' → ℝ)
        (X : Ω' → ℝ → ℝ),
        IsDiffusionSolution P' μ 0 μ (ν : Measure ℝ) B X ∧
        CouplingConverges P P' (fun n => scaled n (Q n)) (fun ω t (_ : Fin 1) => X ω t)) ∧
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : ℝ≥0 → Ω' → ℝ)
      (X : Ω' → ℝ → ℝ),
      IsDiffusionSolution P' μ 0 μ (ν : Measure ℝ) B X →
      CouplingConverges P P' (fun n => scaled n (Q n)) (fun ω t (_ : Fin 1) => X ω t) := by sorry

end MartingaleHT.InfiniteServer
