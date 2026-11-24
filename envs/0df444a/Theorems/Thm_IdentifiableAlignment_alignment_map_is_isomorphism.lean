-- Prove2me | Theorems.Thm_IdentifiableAlignment_alignment_map_is_isomorphism
-- name    : IdentifiableAlignment.alignment_map_is_isomorphism
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:15:46.770435+00:00
-- url     : https://prove2.me/theorems/9a901cd2-162c-49b5-9a4c-81ea17d7ed02
-- title:
--   Proposition 2.3: the alignment map is an isomorphism of the latent mm-spaces
-- statement:
--   Let $\mathcal M$ be a compact connected smooth Riemannian manifold of dimension $d\ge1$, possibly with boundary, with Riemannian distance $d_{\mathcal M}$, and let $P_{\mathcal M}$ be a probability measure on $\mathcal M$ with a smooth positive density (H1). Let $f_a:\mathcal Z_a\to\mathcal M$ and $f_b:\mathcal Z_b\to\mathcal M$ be diffeomorphisms, where each latent space carries the pullback metric $g_a=f_a^*g^{\mathcal M}$, $g_b=f_b^*g^{\mathcal M}$ and its Riemannian distance $d_a$, $d_b$ (H2). Write $P_a=(f_a^{-1})_\#P_{\mathcal M}$, $P_b=(f_b^{-1})_\#P_{\mathcal M}$ and $A=f_b^{-1}\circ f_a$.
--
--   Then:
--   1. a map $A':\mathcal Z_a\to\mathcal Z_b$ satisfies $f_b\circ A'=f_a$ if and only if $A'=A$, so the alignment map exists and is unique;
--   2. $A$ is smooth and $A^*g_b=g_a$, that is, $g_{b,A(z)}(dA_z v,dA_z w)=g_{a,z}(v,w)$ for all $z$ and $v,w\in T_z\mathcal Z_a$;
--   3. $A_\#P_a=P_b$;
--   4. $A$ is an isomorphism of the latent mm-spaces:
--   $$A:(\mathcal Z_a,d_a,P_a)\to(\mathcal Z_b,d_b,P_b)\ \text{is a bijection with}\ d_b(A(z),A(z'))=d_a(z,z'),\ A_\#P_a=P_b.$$
--
--   This is the reason to look for the alignment among isomorphisms of the two latent mm-spaces.
--
--   **Formalization Note** Smoothness of $A$ is listed explicitly because the pullback $A^*g_b$ is defined through the differential of $A$.
-- source:
--   Syrota, Lopez i Serrano, Franck and Hauberg, Identifiable alignment of unpaired representations, arXiv:2611.11460v1 (2026), Section 2, Proposition 2.3, p. 4; appendix form Proposition B.5, Appendix B.1, p. 23

import Mathlib
import Definitions.Def_IdentifiableAlignment_Basic

open MeasureTheory ProbabilityTheory Set Filter Topology Bundle
open scoped ENNReal ContDiff Manifold

namespace IdentifiableAlignment

theorem alignment_map_is_isomorphism {d : ℕ} [NeZero d] {M Za Zb : Type*}
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
    (∀ A : Za → Zb, ⇑fb ∘ A = ⇑fa ↔ A = alignMap fa fb) ∧
    ContMDiff (𝓡∂ d) (𝓡∂ d) ∞ (alignMap fa fb) ∧
    (∀ (z : Za) (v w : TangentSpace (𝓡∂ d) z),
      riemInner (alignMap fa fb z) (mfderiv (𝓡∂ d) (𝓡∂ d) (alignMap fa fb) z v)
        (mfderiv (𝓡∂ d) (𝓡∂ d) (alignMap fa fb) z w) = riemInner z v w) ∧
    (latentLaw P fa).map (alignMap fa fb) = latentLaw P fb ∧
    IsMMIso (latentLaw P fa) (latentLaw P fb) (alignMap fa fb) := by sorry

end IdentifiableAlignment
