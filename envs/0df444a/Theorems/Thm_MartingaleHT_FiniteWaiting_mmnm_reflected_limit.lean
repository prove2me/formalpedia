-- Prove2me | Theorems.Thm_MartingaleHT_FiniteWaiting_mmnm_reflected_limit
-- name    : MartingaleHT.FiniteWaiting.mmnm_reflected_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:04.515971+00:00
-- url     : https://prove2.me/theorems/5543f33b-c370-4f3e-a1cf-5c230092950c
-- title:
--   Theorem 1.2 — in the QED regime the scaled $M/M/n/m_n+M$ queue converges in $D$ to a diffusion reflected at $\kappa$
-- statement:
--   Let $\mu>0$, $\theta\ge0$, $\beta\in\mathbb R$ and $\kappa\ge0$. For each $n\ge1$ let $Q_n$ be the number in system of an $M/M/n/m_n+M$ queue with $n$ servers, a waiting room of size $m_n$, arrival rate $\lambda_n$, service rate $\mu$ and abandonment rate $\theta$, all on one probability space $(\Omega,P)$. Assume the QED scaling
--   $$
--   \frac{n\mu-\lambda_n}{\sqrt n}\to\beta\mu \quad (7),\qquad \frac{m_n}{\sqrt n}\to\kappa \quad (8),
--   $$
--   and let $X_n(t)=(Q_n(t)-n)/\sqrt n$. If $X_n(0)$ converges in distribution to a probability law $\nu$ on $\mathbb R$, then:
--
--   1. there are a probability space $(\Omega',P')$, a standard Brownian motion $B$ and processes $X$, $U$ in $D$, with $X(0)\sim\nu$ independent of $B$, $X\le\kappa$, $U$ nondecreasing and nonnegative, such that almost surely, for every $t\ge0$,
--   $$
--   X(t)=X(0)-\beta\mu t+\sqrt{2\mu}\,B(t)-\int_0^t\big[\mu(X(s)\wedge0)+\theta(X(s)\vee0)\big]\,ds-U(t)\quad(9),
--   \qquad \int_0^\infty\mathbf 1\{X(t)<\kappa\}\,dU(t)=0\quad(10),
--   $$
--   and $X_n\Rightarrow X$ in $D$;
--   2. the limit is unique: any two solutions of (9)–(10) with initial law $\nu$ have the same law on path space.
--
--   The limit is the piecewise-linear-drift diffusion of the Erlang-A model with a reflecting upper barrier at $\kappa$; for $\kappa=0$ (Erlang-B) it is a reflected Ornstein–Uhlenbeck process.
--
--   **Formalization Note** "$X_n(0)\Rightarrow X(0)$" is convergence of $E[g(X_n(0))]$ for every bounded continuous $g$. "$X_n\Rightarrow X$ in $D$" is `BellWilliams2001.ThresholdPolicy.CouplingConverges`: a Skorohod-representation coupling with almost sure uniform convergence on compact intervals, equivalent to $J_1$ weak convergence because the limit has continuous paths. The paper's equivalent description of $X$ by infinitesimal mean $m(x)=-\beta\mu-\mu x$ ($x<0$), $-\beta\mu-\theta x$ ($x>0$), variance $2\mu$ and reflecting barrier $\kappa$ is not formalized separately. Uniqueness is stated as uniqueness in law of $X$. The limit space lives in `Type`. All systems share one probability space, with their own primitives $A_n$, $S_n$, $R_n$; this is no loss since only laws matter. The hypothesis $\kappa\ge0$ follows from (8) and is kept because the paper states it; likewise $\nu((\kappa,\infty))=0$ follows from $Q_n(0)\le n+m_n$ and is not assumed.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 198, Theorem 1.2, (7)–(10); p. 197, §1.2

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_FiniteWaiting_Model
import Definitions.Def_MartingaleHT_FiniteWaiting_Reflection

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MartingaleHT.FiniteWaiting

open BellWilliams2001.ThresholdPolicy ErlangA.Diffusion

/-- **Theorem 1.2** (p. 198). Let `µ > 0`, `θ ≥ 0`, `β ∈ ℝ`, `κ ≥ 0`. For `n ≥ 1` let `Qₙ` be
the number in system of an `M/M/n/mₙ + M` queue with `n` servers, waiting room `mₙ`, arrival rate
`λₙ`, service rate `µ` and abandonment rate `θ`, all systems on one probability space, in the
QED regime `(nµ − λₙ)/√n → βµ` (7) with `mₙ/√n → κ` (8). If `Xₙ(0) = (Qₙ(0) − n)/√n` converges in
distribution to a probability law `ν` on `ℝ`, then
1. there is a solution `(X, U)` of the reflected equation (9)–(10) driven by a standard Brownian
   motion `B`, with `X(0) ∼ ν` independent of `B`, and `Xₙ ⇒ X` in `D` (coupling form);
2. the limit is unique: any two solutions of (9)–(10) with initial law `ν` have the same law of
   `X` on path space. -/
theorem mmnm_reflected_limit (μ β θ κ : ℝ) (hμ : 0 < μ) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (lam : ℕ → ℝ) (m : ℕ → ℕ)
    (h7 : Tendsto (fun n : ℕ => ((n : ℝ) * μ - lam n) / Real.sqrt n) atTop (𝓝 (β * μ)))
    (h8 : Tendsto (fun n : ℕ => (m n : ℝ) / Real.sqrt n) atTop (𝓝 κ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S R : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n →
      IsFiniteWaitingSystem P n (m n) (lam n) μ θ (A n) (S n) (R n) (Q n))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (scaled n (Q n) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (B : ℝ≥0 → Ω' → ℝ)
        (X U : Ω' → ℝ → ℝ),
        IsReflectedSolution P' μ β θ κ (ν : Measure ℝ) B X U ∧
        CouplingConverges P P' (fun n => scaled n (Q n)) (fun ω t (_ : Fin 1) => X ω t)) ∧
    ∀ (Ω₁ : Type) [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) (B₁ : ℝ≥0 → Ω₁ → ℝ)
      (X₁ U₁ : Ω₁ → ℝ → ℝ) (Ω₂ : Type) [MeasurableSpace Ω₂] (P₂ : Measure Ω₂)
      (B₂ : ℝ≥0 → Ω₂ → ℝ) (X₂ U₂ : Ω₂ → ℝ → ℝ),
      IsReflectedSolution P₁ μ β θ κ (ν : Measure ℝ) B₁ X₁ U₁ →
      IsReflectedSolution P₂ μ β θ κ (ν : Measure ℝ) B₂ X₂ U₂ →
      IdentDistrib (fun ω (t : ℝ≥0) => X₁ ω t) (fun ω (t : ℝ≥0) => X₂ ω t) P₁ P₂ := by sorry

end MartingaleHT.FiniteWaiting
