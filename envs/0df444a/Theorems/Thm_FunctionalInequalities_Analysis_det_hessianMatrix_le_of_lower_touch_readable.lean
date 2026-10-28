-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_det_hessianMatrix_le_of_lower_touch_readable
-- name    : FunctionalInequalities.Analysis.det_hessianMatrix_le_of_lower_touch_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:16.713242+00:00
-- url     : https://prove2.me/theorems/0a6a663c-c593-49af-8752-569576e141d5
-- title:
--   Lower Touching Determinant Inequality
-- statement:
--   This is a lower touching test for an Alexandrov solution.
--
--   Let $u,f,\psi:\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))\to\mathbb R$, let $\Omega$ be open, and assume:
--
--   1. $u$ is convex on the whole space;
--   2. for every open $G\subseteq\Omega$, the volume of its `subgradientImage u G` equals
--   $$\int_G \operatorname{ofReal}(f(x))\,d\operatorname{vol}(x);$$
--   3. $x_0\in\Omega$, $f$ is continuous at $x_0$, and $0\le f(x_0)$;
--   4. $\psi$ is $C^2$ at $x_0$ and `hessianMatrix ψ x₀` is positive semidefinite;
--   5. $u(x_0)=\psi(x_0)$ and, almost everywhere near $x_0$, $\psi(x)\le u(x)$.
--
--   Then
--   $$\det(\operatorname{hessianMatrix}(\psi,x_0))\le f(x_0).$$
--
--   This is the formalized weak Alexandrov/viscosity lower inequality. The volume identity uses `ENNReal.ofReal` inside an `L¹` integral, while the conclusion is an ordinary real inequality.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem det_hessianMatrix_le_of_lower_touch {n : ℕ} {u f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
--       (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
--         (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
--           ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--       {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀) (hf0 : 0 ≤ f x₀)
--       (hψ : ContDiffAt ℝ 2 ψ x₀) (hH : (hessianMatrix ψ x₀).PosSemidef)
--       (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, ψ x ≤ u x) :
--       (hessianMatrix ψ x₀).det ≤ f x₀
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`convexOn_quadraticAt`](https://prove2.me/theorems/cc6c84fa-e5eb-4068-927b-9d626453be97), [`subgradientImage_subset_of_le`](https://prove2.me/theorems/48dd6fd6-70dd-48c0-b715-081cfd732396), [`volume_subgradientImage_quadraticAt_aux`](https://prove2.me/theorems/af304715-487f-4a7a-bf76-4a29343dc231), [`hessianMatrix_quadratic`](https://prove2.me/theorems/c1a646b2-00af-48f5-80d5-4c01f3dab8bd), [`local_taylor_two`](https://prove2.me/theorems/4b2efc81-f85a-4a3c-aec5-38e536f55203).
--
--   Previous: [`le_det_hessianMatrix_of_upper_touch`](https://prove2.me/theorems/6c79ec26-adc7-48d0-89d1-5a5ef657b31d) · Next: [`hessianMatrix_quadraticAt`](https://prove2.me/theorems/facc6c9b-040a-4551-a141-72b34dae970f).
--
--   [Source excerpt, lines 655–663](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L655-L663) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L651-L761 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `FunctionalInequalities.Analysis.det_hessianMatrix_le_of_lower_touch`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open FunctionalInequalities.Probability.Stein
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.det_hessianMatrix_le_of_lower_touch_readable {n : ℕ} {u f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀) (hf0 : 0 ≤ f x₀)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hH : (hessianMatrix ψ x₀).PosSemidef)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, ψ x ≤ u x) :
    (hessianMatrix ψ x₀).det ≤ f x₀ := by sorry
