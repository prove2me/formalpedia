-- Prove2me | Theorems.Thm_MartingaleHT_FiniteWaiting_theorem_7_4
-- name    : MartingaleHT.FiniteWaiting.theorem_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:56.086043+00:00
-- url     : https://prove2.me/theorems/629237bd-3d59-46e3-8842-4e47733751e2
-- title:
--   Theorem 7.4 — martingale representation of the scaled $M/M/n/m_n+M$ queue
-- statement:
--   Let $n\ge1$ and let $Q_n$ be the number in system of the $M/M/n/m_n+M$ queue with $n$ servers, waiting room $m_n$, arrival rate $\lambda_n>0$, service rate $\mu>0$ and abandonment rate $\theta\ge0$, constructed from independent rate-1 Poisson processes $A$, $S$, $R$ and an independent initial value $Q_n(0)$. Let $X_n(t)=(Q_n(t)-n)/\sqrt n$, and let $M_{n,1},M_{n,2},M_{n,3}$, $V_n=U_n/\sqrt n$ and $\mathcal F_{n,t}$ be as in (102), (117) and (118). Then:
--
--   1. almost surely, for every $t\ge0$,
--   $$
--   X_n(t)=X_n(0)+M_{n,1}(t)-M_{n,2}(t)-M_{n,3}(t)+\frac{(\lambda_n-\mu n)t}{\sqrt n}-\int_0^t\big[\mu(X_n(s)\wedge0)+\theta X_n(s)^+\big]\,ds-V_n(t);
--   $$
--   2. the σ-algebras $\mathcal F_{n,t}$, $t\ge0$, form a filtration $\mathbb F_n$, and each $M_{n,i}$ is a square-integrable $\mathbb F_n$-martingale with predictable quadratic variation
--   $$
--   \langle M_{n,1}\rangle(t)=\frac{\lambda_n t}{n},\qquad
--   \langle M_{n,2}\rangle(t)=\frac{\mu}{n}\int_0^t(Q_n(s)\wedge n)\,ds,\qquad
--   \langle M_{n,3}\rangle(t)=\frac{\theta}{n}\int_0^t(Q_n(s)-n)^+\,ds,
--   $$
--   with $E[\langle M_{n,i}\rangle(t)]<\infty$ for all $i$ and $t\ge0$.
--
--   This representation writes the scaled queue as an initial value plus martingale noise, a deterministic drift, a Lipschitz feedback term and the scaled blocking process, which is the form Theorem 7.3 maps continuously to $(X_n,V_n)$.
--
--   **Formalization Note** The paper's hypothesis "if $\kappa<\infty$" holds automatically: the waiting room $m_n$ is a natural number. No moment condition on $Q_n(0)$ is needed, since $Q_n(0)\le n+m_n$. $U_n$ uses the left limit $Q_n(s-)$ (see the model's note on (114)); the paper's alternative characterization (115) of $U_n$ is not used. The filtration is (118) augmented by the measurable $P$-null sets, as on the page. "Predictable quadratic variation" is rendered as in the model module: adapted, continuous, nondecreasing and nonnegative, with $M^2-\langle M\rangle$ a martingale.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 252, Theorem 7.4, (116)–(119); pp. 247–248, (102)

import Mathlib
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_FiniteWaiting_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MartingaleHT.FiniteWaiting

open ErlangA.Diffusion

/-- **Theorem 7.4** (p. 252). Let `n ≥ 1` and let `Qₙ` be the `n`-th `M/M/n/mₙ + M` system
(finite waiting room `mₙ`, so `κ < ∞`), with arrival rate `λₙ`, service rate `µ` and abandonment
rate `θ`, built from unit-rate Poisson processes `A`, `S`, `R`. Write `Xₙ = (Qₙ − n)/√n`. Then
1. almost surely, for every `t ≥ 0`, the martingale representation (116) holds:
   `Xₙ(t) = Xₙ(0) + Mₙ,₁(t) − Mₙ,₂(t) − Mₙ,₃(t) + (λₙ − µn)t/√n
     − ∫₀ᵗ [µ(Xₙ(s) ∧ 0) + θ Xₙ(s)⁺] ds − Vₙ(t)`, with `Vₙ = Uₙ/√n` (117);
2. the σ-algebras `ℱₙ,ₜ` of (118), augmented by the `P`-null sets, form a filtration, and with
   respect to it each `Mₙ,ᵢ` is a square-integrable martingale with predictable quadratic variation (119):
   `⟨Mₙ,₁⟩(t) = λₙt/n`, `⟨Mₙ,₂⟩(t) = (µ/n)∫₀ᵗ (Qₙ(s) ∧ n) ds`,
   `⟨Mₙ,₃⟩(t) = (θ/n)∫₀ᵗ (Qₙ(s) − n)⁺ ds`, and `E[⟨Mₙ,ᵢ⟩(t)] < ∞`. -/
theorem theorem_7_4 (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (lam μ θ : ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A S R : Ω → ℝ → ℝ) (Q : Ω → ℝ → ℕ)
    (hsys : IsFiniteWaitingSystem P n m lam μ θ A S R Q) :
    (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      scaled n Q ω t 0 = scaled n Q ω 0 0 + scaledMart1 n lam A ω t
        - scaledMart2 n μ S Q ω t - scaledMart3 n θ R Q ω t
        + (lam - μ * n) * t / Real.sqrt n
        - (∫ s in (0 : ℝ)..t, (μ * min (scaled n Q ω s 0) 0 + θ * max (scaled n Q ω s 0) 0))
        - scaledBlocked n m lam A Q ω t) ∧
    ∃ ℱ : Filtration ℝ≥0 mΩ, (∀ t, ℱ t = genSigma P n lam μ θ A S R Q t) ∧
      (HasPQV ℱ P (fun t ω => scaledMart1 n lam A ω t) (fun t _ => lam * t / n) ∧
        ∀ t : ℝ≥0, Integrable (fun _ : Ω => lam * t / n) P) ∧
      (HasPQV ℱ P (fun t ω => scaledMart2 n μ S Q ω t) (fun t ω => μ / n * busyTime n Q ω t) ∧
        ∀ t : ℝ≥0, Integrable (fun ω => μ / n * busyTime n Q ω t) P) ∧
      (HasPQV ℱ P (fun t ω => scaledMart3 n θ R Q ω t) (fun t ω => θ / n * waitTime n Q ω t) ∧
        ∀ t : ℝ≥0, Integrable (fun ω => θ / n * waitTime n Q ω t) P) := by sorry

end MartingaleHT.FiniteWaiting
