-- Prove2me | Theorems.Thm_OWMR_convex_quantile_contraction
-- name    : OWMR.convex_quantile_contraction
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T20:47:28.99892+00:00
-- url     : https://prove2.me/theorems/58a062b8-42e5-41a9-8a3f-b8f6401577d8
-- title:
--   Lemma D.1 (convex-quantile contraction): if Y has convex quantile Q and Y^[t] has quantile Q(tu), then NV(Y^[t])≤t·NV(Y) and NV(Z+Y^[t])≤(1-t)NV(Z)+t·NV(Z+Y)≤NV(Z+Y)
-- statement:
--   Let $(\Omega,\mathbb P)$ be a probability space, $Y,Y^{[t]},Z$ real random variables, $Q:\mathbb R\to\mathbb R$ nondecreasing and convex on $(0,1)$, $0<t\le1$ and $a,b>0$. Suppose $Y$ is integrable with quantile function $Q$, that is, $Y$ has the law of $Q(V)$ for $V$ uniform on $(0,1)$; $Y^{[t]}$ has quantile function $u\mapsto Q(tu)$ on $(0,1)$; and $Z$ is integrable and independent of $Y$ and of $Y^{[t]}$. With $\mathrm{NV}_{a,b}(X)=\inf_z\mathbb E[a(z-X)^++b(X-z)^+]$ as in (D.1) (the paper's minimum, written as an infimum),
--   $$\mathrm{NV}_{a,b}(Y^{[t]})\le t\,\mathrm{NV}_{a,b}(Y),\qquad \mathrm{NV}_{a,b}(Z+Y^{[t]})\le(1-t)\mathrm{NV}_{a,b}(Z)+t\,\mathrm{NV}_{a,b}(Z+Y)\le\mathrm{NV}_{a,b}(Z+Y).$$
--   The quantile function may be unbounded; only integrability of $Y$ and $Z$ is assumed.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix D, Lemma D.1 (Convex-Quantile Contraction) with the optimized loss (D.1) and inequalities (D.2) and (D.3), p. E.24; proof in Appendix D.1, p. E.27.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace OWMR
theorem convex_quantile_contraction {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Q : ℝ → ℝ) (hQm : MonotoneOn Q (Set.Ioo 0 1))
    (hQc : ConvexOn ℝ (Set.Ioo 0 1) Q) (Y Yt Z : Ω → ℝ) (hY : Measurable Y)
    (hYt : Measurable Yt) (hZ : Measurable Z) (hYi : Integrable Y P) (hZi : Integrable Z P)
    (t a b : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hYlaw : P.map Y = (volume.restrict (Set.Ioo 0 1)).map Q)
    (hYtlaw : P.map Yt = (volume.restrict (Set.Ioo 0 1)).map (fun u => Q (t * u)))
    (hZY : IndepFun Z Y P) (hZYt : IndepFun Z Yt P) :
    let NV : (Ω → ℝ) → ℝ := fun X =>
      ⨅ z : ℝ, ∫ ω, (a * max (z - X ω) 0 + b * max (X ω - z) 0) ∂P
    NV Yt ≤ t * NV Y ∧
      NV (fun ω => Z ω + Yt ω) ≤ (1 - t) * NV Z + t * NV (fun ω => Z ω + Y ω) ∧
      (1 - t) * NV Z + t * NV (fun ω => Z ω + Y ω) ≤ NV (fun ω => Z ω + Y ω) := by sorry
end OWMR
