-- Prove2me | Theorems.Thm_JHolomorphic_tendsto_eLpNorm_normed_convolution_sub_of_continuous
-- name    : JHolomorphic.tendsto_eLpNorm_normed_convolution_sub_of_continuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T21:21:43.599129+00:00
-- url     : https://prove2.me/theorems/44406167-fe3a-45a0-a59a-d9b9c5cff467
-- title:
--   Normalized bump convolutions of a continuous compactly supported map on $\mathbb{C}$ converge in $L^p$
-- statement:
--   Let $E$ be a real Banach space, let $g:\mathbb{C}\to E$ be continuous with compact support, and let $(\varphi_n)$ be a sequence of smooth bump functions centred at $0$ whose outer radii tend to $0$. Writing $\tilde\varphi_n$ for the normalization of $\varphi_n$ (integral $1$), we have for every exponent $p\in[0,\infty]$
--   $$\|\tilde\varphi_n\star g-g\|_{L^p(\mathbb{C})}\longrightarrow 0\qquad(n\to\infty).$$
--   This is the basic approximation statement for continuous compactly supported maps, used to pass from them to general $L^p$ maps.
--
--   **Formalization Note** The bumps are `φ : ℕ → ContDiffBump (0 : ℂ)` with `Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)`; the convolution is `(φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g` and the norm is `eLpNorm _ p volume`, an extended nonnegative real, so the statement is a limit in `ℝ≥0∞`. No restriction on `p` is needed.
-- source:
--   Standard; cf. L. C. Evans, Partial Differential Equations, Appendix C.5, Theorem 7

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace JHolomorphic

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped Convolution ENNReal

/-- For a continuous compactly supported `g : ℂ → E` and normalized bumps `φ n` whose outer radii
tend to `0`, the convolutions `φ n ⋆ g` converge to `g` in `L^p(ℂ)`, for every exponent `p`. -/
theorem tendsto_eLpNorm_normed_convolution_sub_of_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ≥0∞} (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {g : ℂ → E} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Tendsto (fun n => eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g - g) p volume)
      atTop (𝓝 0) := by
  sorry

end JHolomorphic
