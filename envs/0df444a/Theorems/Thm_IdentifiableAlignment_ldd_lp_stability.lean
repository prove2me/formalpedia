-- Prove2me | Theorems.Thm_IdentifiableAlignment_ldd_lp_stability
-- name    : IdentifiableAlignment.ldd_lp_stability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:20:54.743793+00:00
-- url     : https://prove2.me/theorems/6f622611-ad11-4d75-944f-237a72b926bb
-- title:
--   Proposition B.15: stability of the LDD-LP
-- statement:
--   Let $\mathcal M$ be a compact connected smooth Riemannian manifold of dimension $d\ge1$, possibly with boundary, with Riemannian distance $d_{\mathcal M}$, and let $P_{\mathcal M}$ be a probability measure on $\mathcal M$ with a smooth positive density (H1). Let $f_a:\mathcal Z_a\to\mathcal M$ and $f_b:\mathcal Z_b\to\mathcal M$ be diffeomorphisms, where each latent space carries the pullback metric $g_a=f_a^*g^{\mathcal M}$, $g_b=f_b^*g^{\mathcal M}$ and its Riemannian distance $d_a$, $d_b$ (H2). Write $P_a=(f_a^{-1})_\#P_{\mathcal M}$, $P_b=(f_b^{-1})_\#P_{\mathcal M}$ and $A=f_b^{-1}\circ f_a$. Let $R=\operatorname{diam}\mathcal M$, let $m(t)$ be the margin of the data mm-space, and assume $|\Phi(x,r)-\Phi(x,r')|\le K|r-r'|$ for all $x\in\mathcal M$ and $r,r'\ge0$, where $\Phi(x,r)=P_{\mathcal M}(\bar B_{\mathcal M}(x,r))$. Let $c$ be the LDD-LP cost of $P_a,P_b$.
--   1. For every probability measure $\eta$ on $\mathcal Z_a\times\mathcal Z_b$ and every $t\in(0,R]$ with $m(t)>0$,
--   $$\eta\big(\{(z,w):d_b(w,A(z))\ge t\}\big)\le\frac{K^2}{m(t)^3}\int c\,d\eta.$$
--   2. For any samples $\mathrm z^a\in\mathcal Z_a^n$, $\mathrm z^b\in\mathcal Z_b^n$ ($n\ge1$) with empirical measures $\hat P_a,\hat P_b$, every minimiser $\hat\eta$ of the empirical LDD-LP over $\Pi(\hat P_a,\hat P_b)$ satisfies
--   $$\int c\,d\hat\eta\le2R\Big[W_1(\hat P_a,P_a)+W_1(\hat P_b,P_b)+2\delta\Big],$$
--   where $\delta=\sup_zW_2(\hat\Phi_a(z,\cdot),\Phi_a(z,\cdot))+\sup_wW_2(\hat\Phi_b(w,\cdot),\Phi_b(w,\cdot))$.
--   3. With $B(t)=\frac{K^2}{m(t)^3}$ times the right-hand side of 2 and $d_P$ the Lévy–Prokhorov distance for the metric $\max(d_a,d_b)$,
--   $$d_P(\hat\eta,\eta^\star)\le\inf_t\max\{t,B(t)\}+d_P(\hat P_a,P_a),$$
--   the infimum running over $t\in(0,R]$ with $m(t)>0$.
--
--   **Formalization Note** The paper writes the infimum in 3 over all $t>0$. $B(t)$ is defined only where the margin is (Definition 4.3, $0<t\le R$), and the paper intends it to be infinite where $m(t)=0$. In Lean, real division by $0$ gives $0$, so `ENNReal.ofReal (K ^ 2 / margin P t ^ 3)` would be $0$ there, not $\infty$; including such $t$ would make the bound false. The infimum is therefore taken over $t\in(0,R]$ with $m(t)>0$ (an empty infimum is $+\infty$).
-- source:
--   Syrota, Lopez i Serrano, Franck and Hauberg, Identifiable alignment of unpaired representations, arXiv:2611.11460v1 (2026), Appendix B.3, eq. (11), Proposition B.15, eqs. (12)-(13), p. 30; margin Definition 4.3, eq. (5), p. 6

import Mathlib
import Definitions.Def_IdentifiableAlignment_Basic

open MeasureTheory ProbabilityTheory Set Filter Topology Bundle
open scoped ENNReal ContDiff Manifold

namespace IdentifiableAlignment

theorem ldd_lp_stability {d : ℕ} [NeZero d] {M Za Zb : Type*}
    [MetricSpace M] [ChartedSpace (EuclideanHalfSpace d) M] [IsManifold (𝓡∂ d) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓡∂ d) x)]
    [IsContMDiffRiemannianBundle (𝓡∂ d) ∞ (EuclideanSpace ℝ (Fin d)) (fun x : M => TangentSpace (𝓡∂ d) x)]
    [IsRiemannianManifold (𝓡∂ d) M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [MetricSpace Za] [ChartedSpace (EuclideanHalfSpace d) Za] [IsManifold (𝓡∂ d) ∞ Za]
    [RiemannianBundle (fun x : Za => TangentSpace (𝓡∂ d) x)]
    [IsContMDiffRiemannianBundle (𝓡∂ d) ∞ (EuclideanSpace ℝ (Fin d)) (fun x : Za => TangentSpace (𝓡∂ d) x)]
    [IsRiemannianManifold (𝓡∂ d) Za] [MeasurableSpace Za] [BorelSpace Za]
    [MetricSpace Zb] [ChartedSpace (EuclideanHalfSpace d) Zb] [IsManifold (𝓡∂ d) ∞ Zb]
    [RiemannianBundle (fun x : Zb => TangentSpace (𝓡∂ d) x)]
    [IsContMDiffRiemannianBundle (𝓡∂ d) ∞ (EuclideanSpace ℝ (Fin d)) (fun x : Zb => TangentSpace (𝓡∂ d) x)]
    [IsRiemannianManifold (𝓡∂ d) Zb] [MeasurableSpace Zb] [BorelSpace Zb]
    (P : Measure M) [IsProbabilityMeasure P] (hP : HasSmoothPosDensity d P)
    (fa : Za ≃ₘ^∞⟮𝓡∂ d, 𝓡∂ d⟯ M) (fb : Zb ≃ₘ^∞⟮𝓡∂ d, 𝓡∂ d⟯ M)
    (hfa : IsModelCoordinates fa) (hfb : IsModelCoordinates fb)
    (K : ℝ) (hK : IsLddLipschitz P K) :
    (∀ η : Measure (Za × Zb), IsProbabilityMeasure η → ∀ t : ℝ, 0 < t →
      t ≤ Metric.diam (univ : Set M) → 0 < margin P t →
      η {p | t ≤ dist p.2 (alignMap fa fb p.1)} ≤
        ENNReal.ofReal (K ^ 2 / margin P t ^ 3) * lddLP (latentLaw P fa) (latentLaw P fb) η) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (za : Fin n → Za) (zb : Fin n → Zb) (η : Measure (Za × Zb)),
      IsOptimalCoupling (lddLP (empMeasure za) (empMeasure zb)) (empMeasure za) (empMeasure zb) η →
      lddLP (latentLaw P fa) (latentLaw P fb) η ≤ (ENNReal.ofReal (2 * Metric.diam (univ : Set M)) *
        (w1 (empMeasure za) (latentLaw P fa) + w1 (empMeasure zb) (latentLaw P fb) +
          2 * lddEstError (latentLaw P fa) (empMeasure za) (latentLaw P fb) (empMeasure zb))) ∧
      levyProkhorovEDist η (inducedCoupling (latentLaw P fa) (alignMap fa fb)) ≤
        (⨅ t ∈ {t : ℝ | 0 < t ∧ t ≤ Metric.diam (univ : Set M) ∧ 0 < margin P t},
          max (ENNReal.ofReal t) (ENNReal.ofReal (K ^ 2 / margin P t ^ 3) * (ENNReal.ofReal (2 * Metric.diam (univ : Set M)) *
        (w1 (empMeasure za) (latentLaw P fa) + w1 (empMeasure zb) (latentLaw P fb) +
          2 * lddEstError (latentLaw P fa) (empMeasure za) (latentLaw P fb) (empMeasure zb))))) +
        levyProkhorovEDist (empMeasure za) (latentLaw P fa)) := by sorry

end IdentifiableAlignment
