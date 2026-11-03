-- Prove2me | Theorems.Thm_Grothendieck_integrable_inv_norm_gaussian
-- name    : Grothendieck.integrable_inv_norm_gaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:22:21.235095+00:00
-- url     : https://prove2.me/theorems/c786eaee-a59e-4f5a-be38-a416a8da61b9
-- title:
--   $x\mapsto 1/\lVert x\rVert$ is integrable for the Gaussian on $\mathbb R^r$, $r\ge2$
-- statement:
--   For every integer $r\ge2$, the function $x\mapsto 1/\lVert x\rVert$ is integrable against the standard Gaussian measure $\gamma_r$ on $\mathbb R^r$:
--
--   $$
--   \int_{\mathbb R^r}\frac{d\gamma_r(x)}{\lVert x\rVert}<\infty .
--   $$
--
--   Near the origin $\gamma_r$ is comparable with Lebesgue measure, and $\int_{\lVert x\rVert\le1}\lVert x\rVert^{-1}dx$ is finite exactly when $r\ge2$ (the shell integral is $\int_0^1\rho^{r-2}d\rho$); at $r=1$ it diverges logarithmically. The statement is a sharp threshold in the rank, not a technical convenience.
--
--   Its role is the Laplace-transform route to the matrix Grothendieck identity: writing $1/\lVert X\rVert=\pi^{-1/2}\int_0^\infty s^{-1/2}e^{-s\lVert X\rVert^2}ds$ turns the rounding expectation into a two-parameter Gaussian integral, and justifying the Fubini step that exchanges the $s,t$ integrals with the Gaussian one requires precisely this integrability — for the pair $(Zu,Zv)$, whose law is Gaussian and nondegenerate when $|u\cdot v|<1$. That is why that route proves the identity for $r\ge2$ and needs a separate argument at $r=1$.
--
--   **Formalization Note** The Gaussian on $\mathbb R^r$ is `Measure.pi (fun _ : Fin r => gaussianReal 0 1)`, and the norm is written out as `(∑ i, x i ^ 2) ^ (-(1/2) : ℝ)`. A supporting analytic lemma, not a verbatim statement of the paper.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **`x ↦ 1/‖x‖` is integrable against the standard Gaussian on `R^r` for `r ≥ 2`.** This is the
analytic fact behind the `r ≥ 2` threshold in the Laplace-transform route to the matrix
Grothendieck identity; it is false at `r = 1`, where the integral diverges. -/
theorem integrable_inv_norm_gaussian (r : ℕ) (hr : 2 ≤ r) :
    Integrable (fun x : Fin r → ℝ => (∑ i, x i ^ 2) ^ (-(1 / 2) : ℝ))
      (Measure.pi fun _ : Fin r => gaussianReal 0 1) := by sorry

end Grothendieck
