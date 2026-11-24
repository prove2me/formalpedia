-- Prove2me | Theorems.Thm_IdentifiableAlignment_ldd_lp_unique_coupling
-- name    : IdentifiableAlignment.ldd_lp_unique_coupling
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:18:10.271683+00:00
-- url     : https://prove2.me/theorems/de57fea5-3888-4427-b210-5ce2b32282ea
-- title:
--   Proposition 4.2: under C2 the alignment coupling is the unique LDD-LP optimum
-- statement:
--   Let $\mathcal M$ be a compact connected smooth Riemannian manifold of dimension $d\ge1$, possibly with boundary, with Riemannian distance $d_{\mathcal M}$, and let $P_{\mathcal M}$ be a probability measure on $\mathcal M$ with a smooth positive density (H1). Let $f_a:\mathcal Z_a\to\mathcal M$ and $f_b:\mathcal Z_b\to\mathcal M$ be diffeomorphisms, where each latent space carries the pullback metric $g_a=f_a^*g^{\mathcal M}$, $g_b=f_b^*g^{\mathcal M}$ and its Riemannian distance $d_a$, $d_b$ (H2). Write $P_a=(f_a^{-1})_\#P_{\mathcal M}$, $P_b=(f_b^{-1})_\#P_{\mathcal M}$ and $A=f_b^{-1}\circ f_a$. For $z\in\mathcal Z_a$, $w\in\mathcal Z_b$ let $\Phi_a(z,r)=P_a(\bar B_a(z,r))$, $\Phi_b(w,r)=P_b(\bar B_b(w,r))$ and
--   $$c(z,w)=W_2^2\big(\Phi_a(z,\cdot),\Phi_b(w,\cdot)\big),\qquad J_{\mathrm{LDD}}(\eta)=\int c\,d\eta.$$
--   Assume distinguishable points (C2): the set of $x\in\mathcal M$ whose LDD $\Phi(x,\cdot)=P_{\mathcal M}(\bar B_{\mathcal M}(x,\cdot))$ equals that of some other point is $P_{\mathcal M}$-null. Then $\eta^\star=(\mathrm{id}\times A)_\#P_a$ is the unique optimal coupling of
--   $$\min_{\eta\in\Pi(P_a,P_b)}J_{\mathrm{LDD}}(\eta).$$
--
--   The LDD-LP is a linear program, so under C2 the alignment coupling is the optimum of a convex problem.
-- source:
--   Syrota, Lopez i Serrano, Franck and Hauberg, Identifiable alignment of unpaired representations, arXiv:2611.11460v1 (2026), Section 4.1, Proposition 4.2, eq. (3), p. 6; appendix form Proposition B.10, Appendix B.3, p. 27

import Mathlib
import Definitions.Def_IdentifiableAlignment_Basic

open MeasureTheory ProbabilityTheory Set Filter Topology Bundle
open scoped ENNReal ContDiff Manifold

namespace IdentifiableAlignment

theorem ldd_lp_unique_coupling {d : ℕ} [NeZero d] {M Za Zb : Type*}
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
    (hC2 : DistinguishablePoints P) :
    ∀ η : Measure (Za × Zb),
      IsOptimalCoupling (lddLP (latentLaw P fa) (latentLaw P fb)) (latentLaw P fa) (latentLaw P fb) η ↔
        η = inducedCoupling (latentLaw P fa) (alignMap fa fb) := by sorry

end IdentifiableAlignment
