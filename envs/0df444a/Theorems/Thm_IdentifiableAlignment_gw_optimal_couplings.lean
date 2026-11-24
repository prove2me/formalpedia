-- Prove2me | Theorems.Thm_IdentifiableAlignment_gw_optimal_couplings
-- name    : IdentifiableAlignment.gw_optimal_couplings
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:17:31.648662+00:00
-- url     : https://prove2.me/theorems/630106b5-a35c-4da0-b37f-8cc744ec14e2
-- title:
--   Proposition 4.1: GW optimal couplings are the isomorphism couplings, unique under C1
-- statement:
--   Let $\mathcal M$ be a compact connected smooth Riemannian manifold of dimension $d\ge1$, possibly with boundary, with Riemannian distance $d_{\mathcal M}$, and let $P_{\mathcal M}$ be a probability measure on $\mathcal M$ with a smooth positive density (H1). Let $f_a:\mathcal Z_a\to\mathcal M$ and $f_b:\mathcal Z_b\to\mathcal M$ be diffeomorphisms, where each latent space carries the pullback metric $g_a=f_a^*g^{\mathcal M}$, $g_b=f_b^*g^{\mathcal M}$ and its Riemannian distance $d_a$, $d_b$ (H2). Write $P_a=(f_a^{-1})_\#P_{\mathcal M}$, $P_b=(f_b^{-1})_\#P_{\mathcal M}$ and $A=f_b^{-1}\circ f_a$. Let
--   $$J_{\mathrm{GW}}(\eta)=\iint\big|d_a(z,z')-d_b(w,w')\big|^2\,d\eta(z,w)\,d\eta(z',w'),\qquad \eta\in\Pi(P_a,P_b).$$
--   Then:
--   1. the optimal couplings of $\min_{\eta\in\Pi(P_a,P_b)}J_{\mathrm{GW}}(\eta)$ are exactly the couplings $(\mathrm{id}\times T)_\#P_a$ induced by isomorphisms $T$ of $(\mathcal Z_a,d_a,P_a)$ and $(\mathcal Z_b,d_b,P_b)$;
--   2. under symmetry breaking (C1), the optimal coupling is unique and equals $\eta^\star=(\mathrm{id}\times A)_\#P_a$.
--
--   This makes the alignment coupling the unique target of the Gromov–Wasserstein problem whenever the alignment is identifiable.
-- source:
--   Syrota, Lopez i Serrano, Franck and Hauberg, Identifiable alignment of unpaired representations, arXiv:2611.11460v1 (2026), Section 4, Proposition 4.1, eq. (2), p. 6; appendix form Proposition B.9, Appendix B.3, p. 26

import Mathlib
import Definitions.Def_IdentifiableAlignment_Basic

open MeasureTheory ProbabilityTheory Set Filter Topology Bundle
open scoped ENNReal ContDiff Manifold

namespace IdentifiableAlignment

theorem gw_optimal_couplings {d : ℕ} [NeZero d] {M Za Zb : Type*}
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
    (hfa : IsModelCoordinates fa) (hfb : IsModelCoordinates fb) :
    (∀ η : Measure (Za × Zb),
      IsOptimalCoupling gwCost (latentLaw P fa) (latentLaw P fb) η ↔
        ∃ T : Za → Zb, IsMMIso (latentLaw P fa) (latentLaw P fb) T ∧
          η = inducedCoupling (latentLaw P fa) T) ∧
    (SymmetryBreaking P → ∀ η : Measure (Za × Zb),
      IsOptimalCoupling gwCost (latentLaw P fa) (latentLaw P fb) η ↔
        η = inducedCoupling (latentLaw P fa) (alignMap fa fb)) := by sorry

end IdentifiableAlignment
