-- Prove2me | Theorems.Thm_LargeBSP_Homog_Supplement_lemma_B1
-- name    : LargeBSP.Homog.Supplement.lemma_B1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:58:53.344287+00:00
-- url     : https://prove2.me/theorems/f95137d5-5832-4b4e-b171-e73f5523250b
-- title:
--   Lemma B1, p. A13 — normalized upper order statistics converge to Γ_{k+1}(−log Ψ_α)
-- statement:
--   Let $X_1,X_2,\dots$ be i.i.d. nonnegative valuations with distribution function $F_X$ and finite upper endpoint $\eta_F$. Assume $1-F_X(\eta_F-1/x)=x^{-\alpha}L(x)$ for all large $x$, with $\alpha>0$ and $L$ slowly varying, and let $a_N=\eta_F-F_X^{-1}(1-1/N)$. Then for every integer $k\ge0$ and every real $x$
--   $$\mathbb P\!\left(\frac{X_{(N-k)}-\eta_F}{a_N}\le x\right)\longrightarrow\Gamma_{k+1}\bigl(-\log\Psi_\alpha(x)\bigr),$$
--   where $\Psi_\alpha(x)=e^{-(-x)^\alpha}$ for $x\le0$ and $1$ for $x>0$, and $\Gamma_m(y)=\frac1{(m-1)!}\int_y^\infty e^{-t}t^{m-1}dt$.
--
--   This gives the rate at which the top valuations approach the endpoint, the scale against which the discount of Theorem B1 is measured.
--
--   **Formalization Note** The limit distribution function is continuous, so convergence at every $x$ is convergence in distribution. Nothing is claimed about the joint law for different $k$.
--
--   Differences from the source:
--
--   - encoding: convergence in distribution, written with a distribution function as the limit → pointwise convergence of the distribution functions at every real x; reason: the limit distribution function is continuous everywhere
--   - generalization: 1 − F_X(η_F − 1/x) = x^{-α} L(x), with no range of x given → the identity holds for all sufficiently large x; reason: it is a condition on the tail at the endpoint, and the limit law depends only on that tail; requiring the identity only for large x weakens the hypothesis, so the Lean statement implies the printed one
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, Lemma B1, p. A13

import Mathlib
import Definitions.Def_LargeBSP_Homog_Supplement_Extremes

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- Lemma B1, expressed as convergence of cdfs at every real x; the gamma-transform
limit is continuous everywhere, so this is precisely convergence in distribution. -/
theorem lemma_B1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P)
    (hXlaw : ∀ i, Measure.map (X i) P = ν)
    (hν0 : ν (Set.Iio 0) = 0)
    (hfinite : BddAbove {x : ℝ | cdf ν x < 1})
    (α : ℝ) (L : ℝ → ℝ) (htail : EndpointTail ν α L) :
    ∀ (k : ℕ) (x : ℝ),
      Tendsto (fun N : ℕ => (P {ω |
        (upperOrder (fun i => X i ω) N k - endpoint ν) / extremeScale ν N ≤ x}).toReal)
        atTop (𝓝 (extremeCdf α k x)) := by sorry

end LargeBSP.Homog.Supplement
