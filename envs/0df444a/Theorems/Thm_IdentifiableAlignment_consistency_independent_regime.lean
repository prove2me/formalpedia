-- Prove2me | Theorems.Thm_IdentifiableAlignment_consistency_independent_regime
-- name    : IdentifiableAlignment.consistency_independent_regime
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:20:16.418906+00:00
-- url     : https://prove2.me/theorems/03df0d33-f9b3-4ef5-9c59-8c9fc4a17689
-- title:
--   Proposition B.14: consistency of the empirical minimisers in the independent regime
-- statement:
--   Let $\mathcal M$ be a compact connected smooth Riemannian manifold of dimension $d\ge1$, possibly with boundary, with Riemannian distance $d_{\mathcal M}$, and let $P_{\mathcal M}$ be a probability measure on $\mathcal M$ with a smooth positive density (H1). Let $f_a:\mathcal Z_a\to\mathcal M$ and $f_b:\mathcal Z_b\to\mathcal M$ be diffeomorphisms, where each latent space carries the pullback metric $g_a=f_a^*g^{\mathcal M}$, $g_b=f_b^*g^{\mathcal M}$ and its Riemannian distance $d_a$, $d_b$ (H2). Write $P_a=(f_a^{-1})_\#P_{\mathcal M}$, $P_b=(f_b^{-1})_\#P_{\mathcal M}$ and $A=f_b^{-1}\circ f_a$. Let $(\mathrm z^a_i)_{i\ge1}$ be i.i.d. with law $P_a$ and $(\mathrm z^b_j)_{j\ge1}$ i.i.d. with law $P_b$, the two sequences independent (independent regime), and let $\hat P^n_a=\frac1n\sum_{i\le n}\delta_{\mathrm z^a_i}$, $\hat P^n_b=\frac1n\sum_{j\le n}\delta_{\mathrm z^b_j}$. The empirical problems minimise $J_{\mathrm{GW}}$, $J_\beta$ or $J_{\mathrm{LDD}}$ (with the LDDs of $\hat P^n_a,\hat P^n_b$) over $\Pi(\hat P^n_a,\hat P^n_b)$. Let $\mathcal T$ be a class of continuous maps $\mathcal Z_a\to\mathcal Z_b$, compact in the uniform topology, containing $A$, and let $\eta^\star=(\mathrm{id}\times A)_\#P_a$. As $n\to\infty$:
--   1. under C1, almost surely every sequence $\hat\eta_n$ of global minimisers of the empirical GW problem converges weakly to $\eta^\star$; the same holds, for each fixed $\beta\in(0,1)$, for global minimisers of the empirical $J_\beta$;
--   2. under C2, the same holds for global minimisers of the empirical LDD-LP;
--   3. in each case, if $\hat T_n$ minimises $\int d_b(T(z),w)^2\,d\hat\eta_n(z,w)$ over $T\in\mathcal T$, then $\hat T_n\to A$ uniformly on $\mathcal Z_a$, almost surely.
--
--   **Formalization Note** The almost-sure event is fixed before the sequences of minimisers, which are then arbitrary, as in the proof. The minimiser conditions are imposed for $n\ge1$, where the empirical measures are probability measures. Compactness of $\mathcal T$ is taken in the compact-open topology of $C(\mathcal Z_a,\mathcal Z_b)$, which coincides with the uniform topology because $\mathcal Z_a$ is compact.
-- source:
--   Syrota, Lopez i Serrano, Franck and Hauberg, Identifiable alignment of unpaired representations, arXiv:2611.11460v1 (2026), Section 4.2, p. 7; Appendix B.3, Proposition B.14, p. 28 (proof pp. 28-30)

import Mathlib
import Definitions.Def_IdentifiableAlignment_Basic

open MeasureTheory ProbabilityTheory Set Filter Topology Bundle
open scoped ENNReal ContDiff Manifold

namespace IdentifiableAlignment

theorem consistency_independent_regime {d : ℕ} [NeZero d] {M Za Zb : Type*}
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
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (Xa : ℕ → Ω → Za) (Xb : ℕ → Ω → Zb) (hXam : ∀ i, Measurable (Xa i))
    (hXbm : ∀ j, Measurable (Xb j)) (hXaind : iIndepFun Xa Pr) (hXbind : iIndepFun Xb Pr)
    (hXab : IndepFun (fun ξ i => Xa i ξ) (fun ξ j => Xb j ξ) Pr)
    (hXalaw : ∀ i, Pr.map (Xa i) = latentLaw P fa) (hXblaw : ∀ j, Pr.map (Xb j) = latentLaw P fb)
    (𝒯 : Set C(Za, Zb)) (h𝒯 : IsCompact 𝒯) (hA𝒯 : ∃ T ∈ 𝒯, ⇑T = alignMap fa fb) :
    (SymmetryBreaking P →
      (∀ᵐ ξ ∂Pr, ∀ (ηs : ℕ → Measure (Za × Zb)) (Ts : ℕ → C(Za, Zb)),
        (∀ n, 1 ≤ n → IsOptimalCoupling gwCost (empMeasure (fun i : Fin n => Xa i ξ)) (empMeasure (fun j : Fin n => Xb j ξ)) (ηs n)) →
        WeakTendsto ηs (inducedCoupling (latentLaw P fa) (alignMap fa fb)) ∧
        ((∀ n, 1 ≤ n → IsFitMinimizer 𝒯 (ηs n) (Ts n)) →
          TendstoUniformly (fun n => ⇑(Ts n)) (alignMap fa fb) atTop)) ∧
      ∀ β : ℝ, 0 < β → β < 1 →
      (∀ᵐ ξ ∂Pr, ∀ (ηs : ℕ → Measure (Za × Zb)) (Ts : ℕ → C(Za, Zb)),
        (∀ n, 1 ≤ n → IsOptimalCoupling (fusedCost β (empMeasure (fun i : Fin n => Xa i ξ)) (empMeasure (fun j : Fin n => Xb j ξ))) (empMeasure (fun i : Fin n => Xa i ξ)) (empMeasure (fun j : Fin n => Xb j ξ)) (ηs n)) →
        WeakTendsto ηs (inducedCoupling (latentLaw P fa) (alignMap fa fb)) ∧
        ((∀ n, 1 ≤ n → IsFitMinimizer 𝒯 (ηs n) (Ts n)) →
          TendstoUniformly (fun n => ⇑(Ts n)) (alignMap fa fb) atTop))) ∧
    (DistinguishablePoints P →
      (∀ᵐ ξ ∂Pr, ∀ (ηs : ℕ → Measure (Za × Zb)) (Ts : ℕ → C(Za, Zb)),
        (∀ n, 1 ≤ n → IsOptimalCoupling (lddLP (empMeasure (fun i : Fin n => Xa i ξ)) (empMeasure (fun j : Fin n => Xb j ξ))) (empMeasure (fun i : Fin n => Xa i ξ)) (empMeasure (fun j : Fin n => Xb j ξ)) (ηs n)) →
        WeakTendsto ηs (inducedCoupling (latentLaw P fa) (alignMap fa fb)) ∧
        ((∀ n, 1 ≤ n → IsFitMinimizer 𝒯 (ηs n) (Ts n)) →
          TendstoUniformly (fun n => ⇑(Ts n)) (alignMap fa fb) atTop))) := by sorry

end IdentifiableAlignment
