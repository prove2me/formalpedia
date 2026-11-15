-- Prove2me | Theorems.Thm_LG2021_paper_strong_separation
-- name    : LG2021.paper_strong_separation
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T15:15:36.800312+00:00
-- url     : https://prove2.me/theorems/1b3fe5db-d58d-4280-b7b6-9e869175bf6f
-- title:
--   Explicit-parameter Gaussian-surrogate separation
-- statement:
--   For a globally convex Lipschitz function $f:\mathbb R^d\to\mathbb R$, let $X\sim N(0,I_d)$ and define
--   $$m=\mathbb E f(X),\qquad g_\lambda(z)=m+\frac{\mathbb E f((1-\lambda)X+\lambda z)-m}{\lambda},\qquad \Delta_r=m-\min_{\|x\|\le r}f(x).$$
--   Let $d,n\ge1$ and $D\ge0$. Set
--   $$A=10^6(d+1)(D+1)(n+1),\quad L=32\log A,\quad r=10^5d^2\sqrt{2L},\quad \lambda=(4\cdot10^5dL)^{-1}.$$
--   Suppose $f$ has a global Lipschitz constant $K\le dD/r$. For $Z=\frac{r}{2d}\frac{X}{\|X\|}$ (zero at $X=0$),
--   $$\Pr\!\left(g_\lambda(Z)-f(0)\ge\frac{\Delta_r-1/n}{4096d\sqrt d}\right)\ge\frac1{24}.$$
--   All parameter inequalities and the Gaussian tail estimate are proved. In particular, $\lambda(r/(2d))^2=12500d$. Nonsmooth convex losses are included.
--
--   To allow formalization of the separation argument in Tor Lattimore and András György, *Improved Regret for Zeroth-Order Stochastic Convex Bandits*, COLT 2021, PMLR 134:2938–2964, the derivation uses the centered Gaussian Hessian score $XX^\top-I$ and a direct symmetric-density comparison in the part corresponding to Appendix E. Smoothing supplies the nonsmooth case, and all tail and parameter conditions are explicit. This statement concerns separation; the full regret theorem is stated separately.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory (COLT 2021), Proceedings of Machine Learning Research 134:2938–2964, 2021, Lemma 5 and Appendix E. Separation argument adapted for formalization.

import Mathlib
import Definitions.Def_LG2021_GaussianSeparation
import Definitions.Def_LG2021_GaussianEstimators
open LG2021 LG2021.Concentration MeasureTheory ProbabilityTheory

theorem LG2021.paper_strong_separation {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {f : Space d → ℝ} {K : NNReal}
    (hK : (K : ℝ) ≤ paperLipschitz d D (parameterLog d D n))
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) :
    (1/24 : ℝ) ≤
      (sphereMeasure d (paperRadius d (parameterLog d D n)/(2*(d : ℝ)))).real {z |
        (gaussianGap (paperRadius d (parameterLog d D n)) f-1/(n : ℝ))/
          (4096*(d : ℝ)*Real.sqrt (d : ℝ)) ≤
        surrogate (paperLambda d (parameterLog d D n)) f z-f 0} := by sorry
