-- Prove2me | Theorems.Thm_JHolomorphic_uniformCauchySeqOn_normed_convolution
-- name    : JHolomorphic.uniformCauchySeqOn_normed_convolution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T21:32:49.938995+00:00
-- url     : https://prove2.me/theorems/c946e81d-cf05-4943-a122-df808e2f1156
-- title:
--   Bump convolutions of a compactly supported $W^{1,p}$ map on $\mathbb{C}$, $p>2$, are uniformly Cauchy
-- statement:
--   Let $p>2$, let $E$ be a finite-dimensional real normed space, and let $Y:\mathbb{C}\to E$ have compact support with $Y\in L^p(\mathbb{C})$. Suppose $Y_s,Y_t\in L^p(\mathbb{C};E)$ are weak partial derivatives of $Y$ on all of $\mathbb{C}$. Let $(\varphi_n)$ be smooth bump functions centred at $0$ whose outer radii tend to $0$, and $\tilde\varphi_n$ their normalizations (integral $1$). Then the convolutions $\tilde\varphi_n\star Y$ form a uniformly Cauchy sequence on $\mathbb{C}$: for every $\varepsilon>0$ there is $N$ with
--   $$\sup_{z\in\mathbb{C}}\bigl\|(\tilde\varphi_m\star Y)(z)-(\tilde\varphi_n\star Y)(z)\bigr\|<\varepsilon\qquad(m,n\ge N).$$
--   In particular they converge uniformly to a continuous map. This is the uniform-convergence part of the embedding $W^{1,p}\hookrightarrow C^0$ in dimension two.
--
--   **Formalization Note** The bumps are `φ : ℕ → ContDiffBump (0 : ℂ)` with `Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)`; the convolution is `(φ n).normed volume ⋆[lsmul ℝ ℝ, volume] Y`; weak partials on $\mathbb{C}$ are `HasWeakPartialsOn Set.univ Y Ys Yt`, and $L^p$ membership is `MemLp _ (ENNReal.ofReal p) volume`. The conclusion is `UniformCauchySeqOn _ atTop Set.univ`.
-- source:
--   Standard; cf. L. C. Evans, Partial Differential Equations, §5.6.2, Theorem 5; D. McDuff, D. Salamon, J-holomorphic Curves and Symplectic Topology, Appendix B.1

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace JHolomorphic

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped Convolution

/-- Let `p > 2`. If `Y : ℂ → E` has compact support, lies in `L^p(ℂ)` and has weak partial
derivatives on `ℂ` in `L^p(ℂ)`, then for normalized bumps `φ n` whose outer radii tend to `0`
the convolutions `φ n ⋆ Y` form a uniformly Cauchy sequence on `ℂ`. -/
theorem uniformCauchySeqOn_normed_convolution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (φ : ℕ → ContDiffBump (0 : ℂ)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {Y Ys Yt : ℂ → E} (hYc : HasCompactSupport Y) (hY : MemLp Y (ENNReal.ofReal p) volume)
    (h : HasWeakPartialsOn Set.univ Y Ys Yt) (hs : MemLp Ys (ENNReal.ofReal p) volume)
    (ht : MemLp Yt (ENNReal.ofReal p) volume) :
    UniformCauchySeqOn (fun n => (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] Y) atTop Set.univ := by
  sorry

end JHolomorphic
