-- Prove2me | Theorems.Thm_JRCurvedQFT_SharpTime_theorem_4_2
-- name    : JRCurvedQFT.SharpTime.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:37:36.658008+00:00
-- url     : https://prove2.me/theorems/e50ae416-d040-42c8-b96f-4447d500e5c5
-- title:
--   Theorem 4.2 ($Q$ is symmetric and negative) — $-Q$ is a symmetric, positive operator on $C_c^\infty(\Sigma)\subset\mathcal K_\Sigma$
-- statement:
--   Throughout, $M$ is a quantizable static spacetime (Definition 4.1): a complete, connected, smooth Riemannian manifold of dimension $d$ with a global static Killing flow $\phi_s$ (each $\phi_s$ an isometry), a smooth time function $t$ with $t(\phi_s p)=t(p)+s$, the time-zero slice $\Sigma=\{t=0\}$ orthogonal to the Killing field $\xi$, the regions $\Omega_\pm=\{\pm t>0\}$, the reflection $\theta$ and the lapse $F=\langle\xi,\xi\rangle$; $\mathrm{dvol}$ is its Riemannian volume.
--
--   Let $Q$ be the operator (4.4), i.e. the Laplace–Beltrami operator of $M$ applied to functions constant along the Killing trajectories, and $\mathcal K_\Sigma=L^2(\Sigma,\sqrt{\mathcal G}\,dx)$. Then $-Q$ is a symmetric, positive operator on the domain $C_c^\infty(\Sigma)\subset\mathcal K_\Sigma$:
--
--   1. $C_c^\infty(\Sigma)$ is dense in $\mathcal K_\Sigma$;
--   2. for real $f,h\in C_c^\infty(\Sigma)$,
--   $$\int_\Sigma (Qf)\,h\ \sqrt{\mathcal G}\,dx=\int_\Sigma f\,(Qh)\ \sqrt{\mathcal G}\,dx,\qquad -\int_\Sigma (Qf)\,f\ \sqrt{\mathcal G}\,dx\ \ge 0 .$$
--
--   This is what allows the square roots $\mu=(-Q+m^2)^{1/2}$ and $\omega$ of Theorem 4.3.
--
--   Differences from the source:
--   - reading: the class of f is not specified (the proof writes g ∈ 𝒯_Σ, never defined) → real f ∈ C_c^∞(Σ), encoded by smooth ξ-invariant lifts f : M → ℝ with Σ ∩ tsupport f compact; reason: smallest natural class; it makes density hardest and isometry/membership extend to closures (Reading 2)
--   - encoding: quantizable static spacetime (Definition 4.1) with Example 1.1 → complete connected Riemannian manifold with a global isometric flow φ_s and a smooth time function with t∘φ_s = t + s and ξ ⟂ ker dt on Σ = {t = 0}; reason: equivalent to Definition 4.1 with the uniqueness of t that Example 1.1 needs (Reading 3)
--   - encoding: Q = 𝒢^{−1/2}∂_μ(√𝒢 G^{μν}∂_ν) on functions on Σ (4.4) → the chart Laplace–Beltrami operator of M applied to the ξ-invariant lift; reason: by (4.3), Δ_M = F⁻¹∂_t² + Q and ∂_t of the lift vanishes, so the two operators agree
--   - encoding: symmetric and positive on complex C_c^∞(Σ) → stated for real test functions, with density of their complex span; reason: Q is real, so symmetry and positivity for f + ig follow from the real case by linearity
--   - reading: "symmetric operator on the domain C_c^∞(Σ)" → includes density of the domain; reason: a symmetric operator is densely defined (needed for the Friedrichs extension of Theorem 4.3)
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Theorem 4.2, p. 21

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_IsRiemannianVolume
import Definitions.Def_JRCurvedQFT_SharpTime_IsSliceTestFunction
import Definitions.Def_JRCurvedQFT_SharpTime_sliceMeasure
import Definitions.Def_JRCurvedQFT_SharpTime_laplaceBeltrami
import Definitions.Def_JRCurvedQFT_SharpTime_toKSigma

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

/-- **Theorem 4.2 (Q is symmetric and negative).** `−Q` is a symmetric, positive operator on the
domain `C_c^∞(Σ) ⊂ 𝒦_Σ`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, §4.2, Theorem 4.2, p. 21: "Let (M, g_ab) be a quantizable static spacetime. Then −Q is a
symmetric, positive operator on the domain C_c^∞(Σ) ⊂ 𝒦_Σ."

Setting (Definition 4.1): `M` is a complete, connected, smooth Riemannian manifold of dimension
`d` (charts in `ℝ^d`, smooth metric, distance = Riemannian distance) with a static structure `S`
(flow `φ_s` of the static Killing field, time function `t`, slice `Σ = {t = 0}`), and `μ` is its
Riemannian volume.
Conclusions: (1) the test functions on `Σ` span a dense subspace of `𝒦_Σ = L²(Σ, √𝒢 dx)` (the
domain is dense); (2) for real test functions `f, h` on `Σ`, `∫_Σ (Qf) h √𝒢dx = ∫_Σ f (Qh) √𝒢dx` and
`−∫_Σ (Qf) f √𝒢dx ≥ 0`.

**Formalization Note** `Q f` is the Laplace–Beltrami operator of the ξ-invariant lift, read on `Σ`
((4.3): `Δ_M = F⁻¹∂_t² + Q`, and `∂_t f = 0`). Real test functions suffice: `Q` is real, so symmetry
and positivity on complex `f + ig` follow by linearity. "Positive" means `≥ 0` (the proof shows
`−Q ≥ 0`). -/
theorem theorem_4_2 {d : ℕ} {M : Type} [EMetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (EuclideanSpace ℝ (Fin d))
      (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) M] [CompleteSpace M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (S : StaticStructure (d := d) M) (μ : Measure M) (hμ : IsRiemannianVolume (d := d) μ) :
    Dense ((Submodule.span ℂ {v | ∃ f : M → ℝ, IsSliceTestFunction S f ∧
      v = toKSigma (sliceMeasure S μ) (fun x => (f x : ℂ))} : Submodule ℂ _) :
        Set (Lp ℂ 2 (sliceMeasure S μ))) ∧
    ∀ f h : M → ℝ, IsSliceTestFunction S f → IsSliceTestFunction S h →
      (∫ x, laplaceBeltrami (d := d) f x * h x ∂(sliceMeasure S μ)
        = ∫ x, f x * laplaceBeltrami (d := d) h x ∂(sliceMeasure S μ)) ∧
      0 ≤ -∫ x, laplaceBeltrami (d := d) f x * f x ∂(sliceMeasure S μ) := by sorry

end JRCurvedQFT.SharpTime
