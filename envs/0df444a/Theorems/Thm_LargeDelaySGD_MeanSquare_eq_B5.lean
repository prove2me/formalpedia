-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_eq_B5
-- name    : LargeDelaySGD.MeanSquare.eq_B5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:52.428735+00:00
-- url     : https://prove2.me/theorems/80430be8-9b8b-4f65-bddf-78d6aa0dffb1
-- title:
--   (B.5), App. B.1.1, p. 24 — E f(X_{n+1}) − E f(X_n) ≤ −α_{n+1}E‖∇f(X_n)‖² + L B̄ √B α_{n+1}Σα_{r+1} + L√B α²_{n+1} + 4LB α²_{n+1}
-- statement:
--   Throughout, $d \ge 0$, $X=\mathbb R^d$ with the Euclidean norm $\|\cdot\|_2$; the random function $F(x;\xi)$ lives on a probability space $(\Xi,\mu)$ and $f(x)=\mathbb E_\mu[F(x;\xi)]$; the noise sequence $(\omega_n)_{n\ge0}$ lives on a second probability space $(\Omega,\mathbb P)$, is i.i.d. with law $\mu$, and $X_n$ are the DASGD iterates $X_0=x_0$, $X_{n+1}=X_n-\alpha_{n+1}\nabla F(X_{s(n)},\omega_{n+1})$ with a deterministic delay schedule $s(n)\le n$. Assumption 1 is taken with a bound $B\ge\sup_x\mathbb E\|\nabla F(x;\xi)\|_2^2$ and a Lipschitz constant $L$ of $x\mapsto\mathbb E[\nabla F(x;\xi)]$. Assume only $s(n)\le n$ and $\alpha_n>0$ for all $n$, and let $\bar B$ be any bound with $\mathbb E\|\nabla F(x;\xi)\|_2\le\bar B$ for all $x$. Then for every $n$, $f(X_n)$ and $\|\nabla f(X_n)\|_2^2$ are integrable and
--
--   $$\mathbb E[f(X_{n+1})]-\mathbb E[f(X_n)]\le-\alpha_{n+1}\mathbb E\|\nabla f(X_n)\|_2^2+L\bar B\sqrt B\,\alpha_{n+1}\sum_{r=s(n)}^{n-1}\alpha_{r+1}+L\sqrt B\,\alpha_{n+1}^2+4LB\,\alpha_{n+1}^2.$$
--
--   This is the expected one-step descent inequality of delayed SGD: the usual descent term, a delay penalty, and second-order terms in the step size. Telescoping it gives Lemma 1.
--
--   **Formalization Note.** The constants are the page's, as printed in (B.5). The integrability conjuncts guard against Lean's junk value $0$ for integrals of non-integrable functions.
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1, App. B.1.1, p. 24, (B.5)

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

namespace LargeDelaySGD.MeanSquare

open MeasureTheory ProbabilityTheory

theorem eq_B5 {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (α : ℕ → ℝ) (s : ℕ → ℕ)
    (hs : ∀ n, s n ≤ n) (hα : ∀ n, 0 < α n)
    (ω : ℕ → Ω → Ξ) (hω : IIDNoise P μ ω) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X)
    (Bbar : ℝ) (hBbar : ∀ x, ∫ ξ, ‖stochGrad F x ξ‖ ∂μ ≤ Bbar) :
    ∀ n, Integrable (fun a => objective F μ (X n a)) P ∧
      Integrable (fun a => ‖gradient (objective F μ) (X n a)‖ ^ 2) P ∧
      ∫ a, objective F μ (X (n + 1) a) ∂P - ∫ a, objective F μ (X n a) ∂P ≤
        -α (n + 1) * ∫ a, ‖gradient (objective F μ) (X n a)‖ ^ 2 ∂P
          + L * Bbar * Real.sqrt B * α (n + 1) * ∑ r ∈ Finset.Ico (s n) n, α (r + 1)
          + L * Real.sqrt B * α (n + 1) ^ 2 + 4 * L * B * α (n + 1) ^ 2 := by sorry

end LargeDelaySGD.MeanSquare
