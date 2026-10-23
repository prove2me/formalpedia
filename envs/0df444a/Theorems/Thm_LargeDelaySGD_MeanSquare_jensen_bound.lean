-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_jensen_bound
-- name    : LargeDelaySGD.MeanSquare.jensen_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:42.769868+00:00
-- url     : https://prove2.me/theorems/a3c044a3-40ed-4ae1-8c1f-5b7334c82d91
-- title:
--   App. B.1.1, p. 23 — Jensen bound: under Assumption 1, ‖∇f(x)‖²₂ ≤ B for every x
-- statement:
--   Let $F$ satisfy Assumption 1 on $(\Xi,\mu)$ with second-moment bound $B$, i.e. $\mathbb E\|\nabla F(x;\xi)\|_2^2\le B$ for all $x$, and let $f(x)=\mathbb E[F(x;\xi)]$. Then for every $x\in\mathbb R^d$,
--
--   $$\|\nabla f(x)\|_2^2\le B.$$
--
--   This uniform bound on the true gradient is used throughout the proofs of Lemmas 1 and 2.
--
--   **Formalization Note.** $\nabla f$ is Mathlib's `gradient` of $f$; by Remark 1 it equals $\mathbb E[\nabla F(x;\xi)]$.
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1, App. B.1.1, p. 23, display after (B.2)'s chain ("by Jensen's inequality")

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

namespace LargeDelaySGD.MeanSquare

open MeasureTheory ProbabilityTheory

theorem jensen_bound {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal)
    (hA1 : Assumption1 F μ B L) :
    ∀ x, ‖gradient (objective F μ) x‖ ^ 2 ≤ B := by sorry

end LargeDelaySGD.MeanSquare
