-- Prove2me | Theorems.Thm_IdentifiableAlignment_permutation_regime_exact
-- name    : IdentifiableAlignment.permutation_regime_exact
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:19:39.567605+00:00
-- url     : https://prove2.me/theorems/760d5b16-a87e-4201-b754-57f6a7e91d2a
-- title:
--   Proposition 4.4: exact recovery of the permutation in the permutation regime
-- statement:
--   Let $\mathcal M$ be a compact connected smooth Riemannian manifold of dimension $d\ge1$, possibly with boundary, with Riemannian distance $d_{\mathcal M}$, and let $P_{\mathcal M}$ be a probability measure on $\mathcal M$ with a smooth positive density (H1). Let $f_a:\mathcal Z_a\to\mathcal M$ and $f_b:\mathcal Z_b\to\mathcal M$ be diffeomorphisms, where each latent space carries the pullback metric $g_a=f_a^*g^{\mathcal M}$, $g_b=f_b^*g^{\mathcal M}$ and its Riemannian distance $d_a$, $d_b$ (H2). Write $P_a=(f_a^{-1})_\#P_{\mathcal M}$, $P_b=(f_b^{-1})_\#P_{\mathcal M}$ and $A=f_b^{-1}\circ f_a$. Let $n\ge3$, let $\mathrm z^a_1,\dots,\mathrm z^a_n$ be independent with law $P_a$, let $\sigma$ be a permutation of $\{1,\dots,n\}$, and let $\mathrm z^b_{\sigma(i)}=A(\mathrm z^a_i)$ (permutation regime). Let $\hat P_a=\frac1n\sum_i\delta_{\mathrm z^a_i}$, $\hat P_b=\frac1n\sum_j\delta_{\mathrm z^b_j}$, and let the empirical $J_\beta=(1-\beta)J_{\mathrm{GW}}+\beta J_{\mathrm{LDD}}$ use the LDDs of $\hat P_a$ and $\hat P_b$. Then almost surely, for every $\beta\in[0,1]$, the unique optimal coupling of $\min_{\eta\in\Pi(\hat P_a,\hat P_b)}J_\beta(\eta)$ is
--   $$\eta_\sigma=\frac1n\sum_{i=1}^n\delta_{(\mathrm z^a_i,\,\mathrm z^b_{\sigma(i)})}.$$
--
--   No symmetry-breaking condition is needed.
--
--   **Formalization Note** The empirical LDD of a sample point, $\hat\Phi_a(\mathrm z^a_i,r)=\frac1n\#\{k:C^a_{ik}\le r\}$, is written as the LDD of the empirical measure $\hat P_a$, and couplings are measures on $\mathcal Z_a\times\mathcal Z_b$ rather than $n\times n$ matrices; on the almost-sure event that the sample points are distinct the two descriptions coincide.
-- source:
--   Syrota, Lopez i Serrano, Franck and Hauberg, Identifiable alignment of unpaired representations, arXiv:2611.11460v1 (2026), Section 4.2, Proposition 4.4, p. 7; appendix form Proposition B.12, Appendix B.3, pp. 27-28

import Mathlib
import Definitions.Def_IdentifiableAlignment_Basic

open MeasureTheory ProbabilityTheory Set Filter Topology Bundle
open scoped ENNReal ContDiff Manifold

namespace IdentifiableAlignment

theorem permutation_regime_exact {d : ℕ} [NeZero d] {M Za Zb : Type*}
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
    (Xa : Fin n → Ω → Za) (hXm : ∀ i, Measurable (Xa i)) (hXind : iIndepFun Xa Pr)
    (hXlaw : ∀ i, Pr.map (Xa i) = latentLaw P fa)
    (σ : Equiv.Perm (Fin n)) (Xb : Fin n → Ω → Zb)
    (hσ : ∀ ξ i, Xb (σ i) ξ = alignMap fa fb (Xa i ξ)) :
    ∀ᵐ ξ ∂Pr, ∀ β ∈ Icc (0 : ℝ) 1, ∀ η : Measure (Za × Zb),
      IsOptimalCoupling (fusedCost β (empMeasure (fun i => Xa i ξ)) (empMeasure (fun j => Xb j ξ)))
          (empMeasure (fun i => Xa i ξ)) (empMeasure (fun j => Xb j ξ)) η ↔
        η = empMeasure (fun i => (Xa i ξ, Xb (σ i) ξ)) := by sorry

end IdentifiableAlignment
