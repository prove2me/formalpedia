-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_lemma_1
-- name    : LargeDelaySGD.MeanSquare.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:55.104531+00:00
-- url     : https://prove2.me/theorems/15e4f962-fb49-488f-8987-00ab99ac870c
-- title:
--   Lemma 1, p. 10 — under Assumptions 1–2 and inf f > −∞, Σ_n α_{n+1} E[‖∇f(X_n)‖²₂] < ∞
-- statement:
--   Throughout, $d \ge 0$, $X=\mathbb R^d$ with the Euclidean norm $\|\cdot\|_2$; the random function $F(x;\xi)$ lives on a probability space $(\Xi,\mu)$ and $f(x)=\mathbb E_\mu[F(x;\xi)]$; the noise sequence $(\omega_n)_{n\ge0}$ lives on a second probability space $(\Omega,\mathbb P)$, is i.i.d. with law $\mu$, and $X_n$ are the DASGD iterates $X_0=x_0$, $X_{n+1}=X_n-\alpha_{n+1}\nabla F(X_{s(n)},\omega_{n+1})$ with a deterministic delay schedule $s(n)\le n$. Assumption 1 is taken with a bound $B\ge\sup_x\mathbb E\|\nabla F(x;\xi)\|_2^2$ and a Lipschitz constant $L$ of $x\mapsto\mathbb E[\nabla F(x;\xi)]$. Under Assumptions 1 and 2, if $\inf_{x\in\mathbb R^d}f(x)>-\infty$, then each $\|\nabla f(X_n)\|_2^2$ is integrable and
--
--   $$\sum_{n=0}^\infty\alpha_{n+1}\,\mathbb E\big[\|\nabla f(X_n)\|_2^2\big]<\infty.$$
--
--   A step-size-weighted tail sum of the mean-square gradient norms is finite; combined with $\sum\alpha_{n+1}=\infty$ this already gives $\liminf_n\mathbb E\|\nabla f(X_n)\|_2^2=0$.
--
--   **Formalization Note.** "$\inf f>-\infty$" is `BddBelow (Set.range f)`. The integrability conjunct guards against Lean's junk value $0$ for integrals of non-integrable functions.
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1, p. 10, Lemma 1, eq. (2)

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

namespace LargeDelaySGD.MeanSquare

open MeasureTheory ProbabilityTheory

theorem lemma_1 {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (α : ℕ → ℝ) (s : ℕ → ℕ) (hA2 : Assumption2 α s)
    (hinf : BddBelow (Set.range (objective F μ)))
    (ω : ℕ → Ω → Ξ) (hω : IIDNoise P μ ω) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X) :
    (∀ n, Integrable (fun a => ‖gradient (objective F μ) (X n a)‖ ^ 2) P) ∧
      Summable (fun n => α (n + 1) * ∫ a, ‖gradient (objective F μ) (X n a)‖ ^ 2 ∂P) := by sorry

end LargeDelaySGD.MeanSquare
