-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_eq_B4
-- name    : LargeDelaySGD.MeanSquare.eq_B4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:24:01.363988+00:00
-- url     : https://prove2.me/theorems/724eac58-48cf-4f9c-a14a-974579181de1
-- title:
--   (B.4), App. B.1.1, p. 24 — E‖∇f(X_{s(n)}) − ∇f(X_n)‖₂ ≤ L B̄ Σ_{r=s(n)}^{n−1} α_{r+1}
-- statement:
--   Throughout, $d \ge 0$, $X=\mathbb R^d$ with the Euclidean norm $\|\cdot\|_2$; the random function $F(x;\xi)$ lives on a probability space $(\Xi,\mu)$ and $f(x)=\mathbb E_\mu[F(x;\xi)]$; the noise sequence $(\omega_n)_{n\ge0}$ lives on a second probability space $(\Omega,\mathbb P)$, is i.i.d. with law $\mu$, and $X_n$ are the DASGD iterates $X_0=x_0$, $X_{n+1}=X_n-\alpha_{n+1}\nabla F(X_{s(n)},\omega_{n+1})$ with a deterministic delay schedule $s(n)\le n$. Assumption 1 is taken with a bound $B\ge\sup_x\mathbb E\|\nabla F(x;\xi)\|_2^2$ and a Lipschitz constant $L$ of $x\mapsto\mathbb E[\nabla F(x;\xi)]$. Assume only $s(n)\le n$ and $\alpha_n>0$ for all $n$ from Assumption 2, and let $\bar B$ be any bound with $\mathbb E\|\nabla F(x;\xi)\|_2\le\bar B$ for all $x$. Then for every $n$, the random variable $\|\nabla f(X_{s(n)})-\nabla f(X_n)\|_2$ is integrable and
--
--   $$\mathbb E\big[\|\nabla f(X_{s(n)})-\nabla f(X_n)\|_2\big]\le L\bar B\sum_{r=s(n)}^{n-1}\alpha_{r+1}.$$
--
--   This controls the staleness of the delayed gradient: the error from evaluating at $X_{s(n)}$ instead of $X_n$ is at most the step sizes accumulated during the delay.
--
--   **Formalization Note.** The integrability conjunct guards against Lean's convention that the integral of a non-integrable function is $0$. The empty sum ($s(n)=n$, no delay) is $0$.
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1, App. B.1.1, p. 24, (B.3)–(B.4)

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

namespace LargeDelaySGD.MeanSquare

open MeasureTheory ProbabilityTheory

theorem eq_B4 {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (α : ℕ → ℝ) (s : ℕ → ℕ)
    (hs : ∀ n, s n ≤ n) (hα : ∀ n, 0 < α n)
    (ω : ℕ → Ω → Ξ) (hω : IIDNoise P μ ω) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X)
    (Bbar : ℝ) (hBbar : ∀ x, ∫ ξ, ‖stochGrad F x ξ‖ ∂μ ≤ Bbar) :
    ∀ n, Integrable (fun a => ‖gradient (objective F μ) (X (s n) a) -
        gradient (objective F μ) (X n a)‖) P ∧
      ∫ a, ‖gradient (objective F μ) (X (s n) a) - gradient (objective F μ) (X n a)‖ ∂P ≤
        L * Bbar * ∑ r ∈ Finset.Ico (s n) n, α (r + 1) := by sorry

end LargeDelaySGD.MeanSquare
