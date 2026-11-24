-- Prove2me | Theorems.Thm_IdentifiableAlignment_fused_gw_unique_minimiser
-- name    : IdentifiableAlignment.fused_gw_unique_minimiser
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:18:37.102039+00:00
-- url     : https://prove2.me/theorems/e2954956-b066-45ad-980f-f0c584a21788
-- title:
--   Proposition B.17: under C1 the alignment coupling uniquely minimises $J_\beta$ for $\beta<1$
-- statement:
--   Let $\mathcal M$ be a compact connected smooth Riemannian manifold of dimension $d\ge1$, possibly with boundary, with Riemannian distance $d_{\mathcal M}$, and let $P_{\mathcal M}$ be a probability measure on $\mathcal M$ with a smooth positive density (H1). Let $f_a:\mathcal Z_a\to\mathcal M$ and $f_b:\mathcal Z_b\to\mathcal M$ be diffeomorphisms, where each latent space carries the pullback metric $g_a=f_a^*g^{\mathcal M}$, $g_b=f_b^*g^{\mathcal M}$ and its Riemannian distance $d_a$, $d_b$ (H2). Write $P_a=(f_a^{-1})_\#P_{\mathcal M}$, $P_b=(f_b^{-1})_\#P_{\mathcal M}$ and $A=f_b^{-1}\circ f_a$. For $\beta\in[0,1]$ let $J_\beta=(1-\beta)J_{\mathrm{GW}}+\beta J_{\mathrm{LDD}}$, with $J_{\mathrm{GW}}$ the Gromov–Wasserstein objective and $J_{\mathrm{LDD}}$ the LDD-LP objective built from the LDDs of $P_a$ and $P_b$. Under symmetry breaking (C1), for every $\beta\in[0,1)$,
--   $$\eta^\star=(\mathrm{id}\times A)_\#P_a\ \text{is the unique minimiser of }J_\beta\text{ over }\Pi(P_a,P_b).$$
--
--   So, under C1, a solver may move $\beta$ anywhere in $[0,1)$ without moving the minimiser; the endpoint $\beta=1$ (the pure LDD-LP) is not covered here and needs C2 instead (Proposition 4.2).
-- source:
--   Syrota, Lopez i Serrano, Franck and Hauberg, Identifiable alignment of unpaired representations, arXiv:2611.11460v1 (2026), Section 4.1, eq. (4), p. 6; Appendix B.3.1, Proposition B.17, p. 31

import Mathlib
import Definitions.Def_IdentifiableAlignment_Basic

open MeasureTheory ProbabilityTheory Set Filter Topology Bundle
open scoped ENNReal ContDiff Manifold

namespace IdentifiableAlignment

theorem fused_gw_unique_minimiser {d : ℕ} [NeZero d] {M Za Zb : Type*}
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
    (hC1 : SymmetryBreaking P) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∀ η : Measure (Za × Zb),
      IsOptimalCoupling (fusedCost β (latentLaw P fa) (latentLaw P fb)) (latentLaw P fa) (latentLaw P fb) η ↔
        η = inducedCoupling (latentLaw P fa) (alignMap fa fb) := by sorry

end IdentifiableAlignment
