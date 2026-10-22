-- Prove2me | Theorems.Thm_JHolomorphic_tendsto_eLpNorm_normed_convolution_sub
-- name    : JHolomorphic.tendsto_eLpNorm_normed_convolution_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T21:29:19.773244+00:00
-- url     : https://prove2.me/theorems/15291e13-2ffa-4b5a-8893-13214a957692
-- title:
--   Normalized bump convolutions on $\mathbb{C}$ converge in $L^p$, $1\le p<\infty$
-- statement:
--   Let $E$ be a real Banach space, $1\le p<\infty$, and $f\in L^p(\mathbb{C};E)$. Let $(\varphi_n)$ be a sequence of smooth bump functions centred at $0$ whose outer radii tend to $0$, and write $\tilde\varphi_n$ for the normalization of $\varphi_n$ (integral $1$). Then
--   $$\|\tilde\varphi_n\star f-f\|_{L^p(\mathbb{C})}\longrightarrow 0\qquad(n\to\infty).$$
--   This is the standard $L^p$ approximation by mollification on the plane, for vector-valued maps.
--
--   **Formalization Note** The bumps are `φ : ℕ → ContDiffBump (0 : ℂ)` with `Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)`; the convolution is `(φ n).normed volume ⋆[lsmul ℝ ℝ, volume] f`, the hypothesis is `MemLp f p volume` with `1 ≤ p` and `p ≠ ⊤`, and the norm is `eLpNorm _ p volume`, so the statement is a limit in `ℝ≥0∞`.
-- source:
--   Standard; cf. L. C. Evans, Partial Differential Equations, Appendix C.5, Theorem 7; H. Brezis, Functional Analysis, Sobolev Spaces and PDE, Theorem 4.22

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace JHolomorphic

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped Convolution ENNReal

/-- For `1 ≤ p < ∞`, `f ∈ L^p(ℂ; E)` and normalized bumps `φ n` whose outer radii tend to `0`,
the convolutions `φ n ⋆ f` converge to `f` in `L^p(ℂ)`. -/
theorem tendsto_eLpNorm_normed_convolution_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (φ : ℕ → ContDiffBump (0 : ℂ)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {f : ℂ → E} (hf : MemLp f p volume) :
    Tendsto (fun n => eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] f - f) p volume)
      atTop (𝓝 0) := by
  sorry

end JHolomorphic
