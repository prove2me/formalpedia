-- Prove2me | Theorems.Thm_MathlibGap_gaussianReal_prod_map_sq_add_sq
-- name    : MathlibGap.gaussianReal_prod_map_sq_add_sq
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T15:11:07.816013+00:00
-- url     : https://prove2.me/theorems/0391e301-1307-4be5-9b05-0f25198897a0
-- title:
--   If $X, Y$ are i.i.d. $N(0,v)$ then $X^2+Y^2$ is exponential with rate $1/(2v)$
-- statement:
--   Let $v > 0$ and let $X, Y$ be independent real Gaussian random variables with mean $0$ and variance $v$. Then $X^2 + Y^2$ has the exponential distribution with rate $1/(2v)$:
--
--   $$
--   \mathbb{P}\left(X^2 + Y^2 \in A\right) = \int_A \mathbf{1}_{x > 0}\, \frac{1}{2v}\, e^{-x/(2v)}\, dx
--   $$
--
--   for every Borel set $A \subseteq \mathbb{R}$.
--
--   Equivalently, the squared modulus of a circular complex Gaussian with $\mathbb{E}|Z|^2 = 2v$ is exponential with mean $2v$. This is the classical fact behind Rayleigh's law for speckle intensities, and it is the distributional core of eq. (1) of Schomerus, van Bemmel and Beenakker.
--
--   **Formalization Note** The law of $(X, Y)$ is `(gaussianReal 0 v).prod (gaussianReal 0 v)` and the statement is an equality of measures on $\mathbb{R}$, with the density written via `withDensity`.
-- source:
--   H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 1, eq. (1) (Rayleigh's law); classical result for the chi-squared distribution with two degrees of freedom

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MathlibGap

theorem gaussianReal_prod_map_sq_add_sq (v : NNReal) (hv : v ≠ 0) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)).map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) =
      (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal
        (if 0 < x then (2 * (v : ℝ))⁻¹ * Real.exp (-(2 * (v : ℝ))⁻¹ * x) else 0)) := by sorry

end MathlibGap
