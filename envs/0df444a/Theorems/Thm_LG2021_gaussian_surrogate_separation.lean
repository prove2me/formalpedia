-- Prove2me | Theorems.Thm_LG2021_gaussian_surrogate_separation
-- name    : LG2021.gaussian_surrogate_separation
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T15:09:41.222945+00:00
-- url     : https://prove2.me/theorems/4489f94f-d5fb-4ee3-a0bf-ac599ef0182e
-- title:
--   Gaussian-surrogate separation for nonsmooth convex losses
-- statement:
--   For a globally convex Lipschitz function $f:\mathbb R^d\to\mathbb R$, let $X\sim N(0,I_d)$ and define
--   $$m=\mathbb E f(X),\qquad g_\lambda(z)=m+\frac{\mathbb E f((1-\lambda)X+\lambda z)-m}{\lambda},\qquad \Delta_r=m-\min_{\|x\|\le r}f(x).$$
--   Let $d\ge1$, let $K\ge0$ be a Lipschitz constant for $f$, and let $0<\lambda<1$, $R>0$, $B\ge0$. Suppose
--   $$\frac{(1-(1-\lambda)^2)B^2}{2(1-\lambda)^2}\le1,\quad \frac{(\lambda R)^2}{2(1-\lambda)^2}\le1,\quad \Pr(\|X\|>B)\le\delta,$$
--   $$4\le\frac{\lambda e^{-2}R^2}{128d},\qquad \frac{\lambda}{2}e^{-2}\,2K\sqrt{d\delta}\,R^2\le\frac{\varepsilon}{4096d\sqrt d}.$$
--   For $Z=RX/\|X\|$ (defined to be zero when $X=0$),
--   $$\Pr\!\left(g_\lambda(Z)-f(0)\ge\frac{\Delta_{2dR}-\varepsilon}{4096d\sqrt d}\right)\ge\frac1{24}.$$
--   No differentiability hypothesis is imposed on $f$. The proof uses positive Hessians, Gaussian integration by parts and symmetric density comparison, followed by double Gaussian smoothing and a closed-event limit.
--
--   To allow formalization of the separation argument in Tor Lattimore and András György, *Improved Regret for Zeroth-Order Stochastic Convex Bandits*, COLT 2021, PMLR 134:2938–2964, the derivation uses the centered Gaussian Hessian score $XX^\top-I$ and a direct symmetric-density comparison in the part corresponding to Appendix E. Smoothing supplies the nonsmooth case, and all tail and parameter conditions are explicit. This statement concerns separation; the full regret theorem is stated separately.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory (COLT 2021), Proceedings of Machine Learning Research 134:2938–2964, 2021, Lemma 5 and Appendix E. Separation argument adapted for formalization.

import Mathlib
import Definitions.Def_LG2021_GaussianSeparation
import Definitions.Def_LG2021_GaussianEstimators
open LG2021 LG2021.Concentration MeasureTheory ProbabilityTheory

theorem LG2021.gaussian_surrogate_separation {d : ℕ} (hd : 0 < d) {f : Space d → ℝ}
    {K : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    {lambda R B delta eps : ℝ} (hl : 0 < lambda) (hl1 : lambda < 1) (hR : 0 < R)
    (hB : 0 ≤ B) (hvar : (1-(1-lambda)^2)*B^2/(2*(1-lambda)^2) ≤ 1)
    (hshift : (lambda*R)^2/(2*(1-lambda)^2) ≤ 1)
    (htail : (gaussian d).real {x : Space d | B < ‖x‖} ≤ delta)
    (hgain : 4 ≤ (lambda/2)*Real.exp (-2)*(R^2/(64*(d : ℝ))))
    (herr : ((lambda/2)*Real.exp (-2)*(2*(K : ℝ)*Real.sqrt ((d : ℝ)*delta)))*R^2 ≤
      eps/(4096*(d : ℝ)*Real.sqrt (d : ℝ))) :
    (1/24 : ℝ) ≤ (sphereMeasure d R).real {z |
      (gaussianGap (2*(d : ℝ)*R) f-eps)/(4096*(d : ℝ)*Real.sqrt (d : ℝ)) ≤
        surrogate lambda f z-f 0} := by sorry
