-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_lemma_2
-- name    : LargeDelaySGD.MeanSquare.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:56.484996+00:00
-- url     : https://prove2.me/theorems/2878672e-1645-4f6f-b8ab-20f57b64c251
-- title:
--   Lemma 2, p. 11 — under Assumptions 1–2, |E‖∇f(X_{n+1})‖²₂ − E‖∇f(X_n)‖²₂| ≤ C α_{n+1} for a constant C > 0
-- statement:
--   Throughout, $d \ge 0$, $X=\mathbb R^d$ with the Euclidean norm $\|\cdot\|_2$; the random function $F(x;\xi)$ lives on a probability space $(\Xi,\mu)$ and $f(x)=\mathbb E_\mu[F(x;\xi)]$; the noise sequence $(\omega_n)_{n\ge0}$ lives on a second probability space $(\Omega,\mathbb P)$, is i.i.d. with law $\mu$, and $X_n$ are the DASGD iterates $X_0=x_0$, $X_{n+1}=X_n-\alpha_{n+1}\nabla F(X_{s(n)},\omega_{n+1})$ with a deterministic delay schedule $s(n)\le n$. Assumption 1 is taken with a bound $B\ge\sup_x\mathbb E\|\nabla F(x;\xi)\|_2^2$ and a Lipschitz constant $L$ of $x\mapsto\mathbb E[\nabla F(x;\xi)]$. Under Assumptions 1 and 2, each $\|\nabla f(X_n)\|_2^2$ is integrable, and there exists a constant $C>0$ such that for every $n$,
--
--   $$\Big|\mathbb E\big[\|\nabla f(X_{n+1})\|_2^2\big]-\mathbb E\big[\|\nabla f(X_n)\|_2^2\big]\Big|\le C\,\alpha_{n+1}.$$
--
--   Successive mean-square gradient norms cannot change faster than the step size; this rules out the oscillating sequences for which a finite weighted sum (Lemma 1) does not imply convergence.
--
--   **Formalization Note.** The integrability conjunct guards against Lean's junk value $0$ for integrals of non-integrable functions. $C$ may depend on the model data ($F$, $\mu$, $B$, $L$), as on the page.
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1, p. 11, Lemma 2

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

namespace LargeDelaySGD.MeanSquare

open MeasureTheory ProbabilityTheory

theorem lemma_2 {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (α : ℕ → ℝ) (s : ℕ → ℕ) (hA2 : Assumption2 α s)
    (ω : ℕ → Ω → Ξ) (hω : IIDNoise P μ ω) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X) :
    (∀ n, Integrable (fun a => ‖gradient (objective F μ) (X n a)‖ ^ 2) P) ∧
      ∃ C > (0 : ℝ), ∀ n, |∫ a, ‖gradient (objective F μ) (X (n + 1) a)‖ ^ 2 ∂P -
        ∫ a, ‖gradient (objective F μ) (X n a)‖ ^ 2 ∂P| ≤ C * α (n + 1) := by sorry

end LargeDelaySGD.MeanSquare
