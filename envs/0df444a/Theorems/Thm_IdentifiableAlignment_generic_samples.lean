-- Prove2me | Theorems.Thm_IdentifiableAlignment_generic_samples
-- name    : IdentifiableAlignment.generic_samples
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:19:12.361197+00:00
-- url     : https://prove2.me/theorems/49d4ef25-04f2-468f-a9e9-97850eb96903
-- title:
--   Lemma B.11: generic samples have distinct points, distances and distance rows
-- statement:
--   Let $\mathcal M$ be a compact connected smooth Riemannian manifold of dimension $d\ge1$, possibly with boundary, with Riemannian distance $d_{\mathcal M}$, and let $P_{\mathcal M}$ be a probability measure on $\mathcal M$ with a smooth positive density (H1). Let $f_a:\mathcal Z_a\to\mathcal M$ and $f_b:\mathcal Z_b\to\mathcal M$ be diffeomorphisms, where each latent space carries the pullback metric $g_a=f_a^*g^{\mathcal M}$, $g_b=f_b^*g^{\mathcal M}$ and its Riemannian distance $d_a$, $d_b$ (H2). Write $P_a=(f_a^{-1})_\#P_{\mathcal M}$, $P_b=(f_b^{-1})_\#P_{\mathcal M}$ and $A=f_b^{-1}\circ f_a$. Let $n\ge3$ and let $\mathrm z_1,\dots,\mathrm z_n$ be independent random points of $\mathcal Z_a$ with law $P_a$. Then, almost surely:
--   1. the points $\mathrm z_1,\dots,\mathrm z_n$ are distinct;
--   2. the $\binom n2$ distances $d_a(\mathrm z_i,\mathrm z_j)$, $i<j$, are distinct;
--   3. for $i\neq j$ the rows $\{d_a(\mathrm z_i,\mathrm z_l):l\neq i\}$ and $\{d_a(\mathrm z_j,\mathrm z_l):l\neq j\}$ of the distance matrix differ as multisets;
--   4. the only permutation $\tau$ of $\{1,\dots,n\}$ with $d_a(\mathrm z_{\tau(i)},\mathrm z_{\tau(j)})=d_a(\mathrm z_i,\mathrm z_j)$ for all $i,j$ is the identity.
-- source:
--   Syrota, Lopez i Serrano, Franck and Hauberg, Identifiable alignment of unpaired representations, arXiv:2611.11460v1 (2026), Appendix B.3, Lemma B.11, p. 27

import Mathlib
import Definitions.Def_IdentifiableAlignment_Basic

open MeasureTheory ProbabilityTheory Set Filter Topology Bundle
open scoped ENNReal ContDiff Manifold

namespace IdentifiableAlignment

theorem generic_samples {d : ℕ} [NeZero d] {M Za Zb : Type*}
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
    (n : ℕ) (hn : 3 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : Fin n → Ω → Za) (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X Pr)
    (hXlaw : ∀ i, Pr.map (X i) = latentLaw P fa) :
    ∀ᵐ ξ ∂Pr,
      Function.Injective (fun i => X i ξ) ∧
      (∀ i j k l : Fin n, i < j → k < l → (i, j) ≠ (k, l) →
        dist (X i ξ) (X j ξ) ≠ dist (X k ξ) (X l ξ)) ∧
      (∀ i j : Fin n, i ≠ j →
        (Finset.univ.erase i).val.map (fun l => dist (X i ξ) (X l ξ)) ≠
          (Finset.univ.erase j).val.map (fun l => dist (X j ξ) (X l ξ))) ∧
      (∀ τ : Equiv.Perm (Fin n), (∀ i j, dist (X (τ i) ξ) (X (τ j) ξ) = dist (X i ξ) (X j ξ)) →
        τ = 1) := by sorry

end IdentifiableAlignment
