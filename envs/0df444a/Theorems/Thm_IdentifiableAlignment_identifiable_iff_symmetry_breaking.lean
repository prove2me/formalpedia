-- Prove2me | Theorems.Thm_IdentifiableAlignment_identifiable_iff_symmetry_breaking
-- name    : IdentifiableAlignment.identifiable_iff_symmetry_breaking
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:16:19.399862+00:00
-- url     : https://prove2.me/theorems/84ccdaf9-e4d0-45cd-b199-7846d330d690
-- title:
--   Proposition 3.1: isomorphisms come from symmetries; $A$ is identifiable iff C1
-- statement:
--   Let $\mathcal M$ be a compact connected smooth Riemannian manifold of dimension $d\ge1$, possibly with boundary, with Riemannian distance $d_{\mathcal M}$, and let $P_{\mathcal M}$ be a probability measure on $\mathcal M$ with a smooth positive density (H1). Let $f_a:\mathcal Z_a\to\mathcal M$ and $f_b:\mathcal Z_b\to\mathcal M$ be diffeomorphisms, where each latent space carries the pullback metric $g_a=f_a^*g^{\mathcal M}$, $g_b=f_b^*g^{\mathcal M}$ and its Riemannian distance $d_a$, $d_b$ (H2). Write $P_a=(f_a^{-1})_\#P_{\mathcal M}$, $P_b=(f_b^{-1})_\#P_{\mathcal M}$ and $A=f_b^{-1}\circ f_a$.
--
--   Then the isomorphisms $(\mathcal Z_a,d_a,P_a)\to(\mathcal Z_b,d_b,P_b)$ are exactly the maps
--   $$f_b^{-1}\circ S\circ f_a,\qquad S\in\operatorname{Aut}(\mathcal M,d_{\mathcal M},P_{\mathcal M}),$$
--   where $\operatorname{Aut}$ is the group of distance-preserving bijections of $\mathcal M$ preserving $P_{\mathcal M}$. Consequently every isomorphism of the latent mm-spaces equals $A$ if and only if the identity is the only symmetry of the data mm-space (condition C1).
--
--   The identifiability of the alignment from unpaired data is therefore a property of the data-generating process alone.
-- source:
--   Syrota, Lopez i Serrano, Franck and Hauberg, Identifiable alignment of unpaired representations, arXiv:2611.11460v1 (2026), Section 3, Proposition 3.1, p. 5; appendix form Proposition B.7, Appendix B.2, p. 23

import Mathlib
import Definitions.Def_IdentifiableAlignment_Basic

open MeasureTheory ProbabilityTheory Set Filter Topology Bundle
open scoped ENNReal ContDiff Manifold

namespace IdentifiableAlignment

theorem identifiable_iff_symmetry_breaking {d : ℕ} [NeZero d] {M Za Zb : Type*}
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
    (∀ T : Za → Zb, IsMMIso (latentLaw P fa) (latentLaw P fb) T ↔
      ∃ S : M → M, IsSymmetry P S ∧ T = ⇑fb.symm ∘ S ∘ ⇑fa) ∧
    ((∀ T : Za → Zb, IsMMIso (latentLaw P fa) (latentLaw P fb) T → T = alignMap fa fb) ↔
      SymmetryBreaking P) := by sorry

end IdentifiableAlignment
