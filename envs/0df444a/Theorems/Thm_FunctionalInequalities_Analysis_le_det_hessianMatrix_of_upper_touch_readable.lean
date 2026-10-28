-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_le_det_hessianMatrix_of_upper_touch_readable
-- name    : FunctionalInequalities.Analysis.le_det_hessianMatrix_of_upper_touch_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:56.821636+00:00
-- url     : https://prove2.me/theorems/6c79ec26-adc7-48d0-89d1-5a5ef657b31d
-- title:
--   Alexandrov Upper Touching Determinant Inequality
-- statement:
--   Let $u,f:\mathbb R^n\to\mathbb R$, let $\Omega$ be open, and assume $u$ is convex. Suppose that for every open $G\subseteq\Omega$,
--   $$\operatorname{vol}(\partial u(G))=\int_G\operatorname{ofReal}(f(x))\,dx$$
--   with the integral interpreted in $[0,\infty]$. If $x_0\in\Omega$, $f$ is continuous at $x_0$, $\psi\in C^2$ at $x_0$, $u(x_0)=\psi(x_0)$, and $u\le\psi$ near $x_0$, then
--
--   $$f(x_0)\le\det\operatorname{hessianMatrix}(\psi)(x_0).$$
--
--   This is the stated Alexandrov-to-viscosity determinant inequality.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem le_det_hessianMatrix_of_upper_touch {n : ℕ} {u f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
--       (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
--         (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
--           ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--       {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀)
--       (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
--       f x₀ ≤ (hessianMatrix ψ x₀).det
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Selected supporting theorems: [`convexOn_quadraticAt`](https://prove2.me/theorems/cc6c84fa-e5eb-4068-927b-9d626453be97), [`posSemidef_hessianMatrix_of_upper_touch`](https://prove2.me/theorems/c0934c18-f16d-42fc-a97b-28fa4ccb6c6d), [`subgradientImage_subset_of_le`](https://prove2.me/theorems/48dd6fd6-70dd-48c0-b715-081cfd732396), [`volume_subgradientImage_quadraticAt_aux`](https://prove2.me/theorems/af304715-487f-4a7a-bf76-4a29343dc231), [`hessianMatrix_quadratic`](https://prove2.me/theorems/c1a646b2-00af-48f5-80d5-4c01f3dab8bd).
--
--   Previous: [`local_taylor_two`](https://prove2.me/theorems/4b2efc81-f85a-4a3c-aec5-38e536f55203) · Next: [`det_hessianMatrix_le_of_lower_touch`](https://prove2.me/theorems/0a6a663c-c593-49af-8752-569576e141d5).
--
--   [Source excerpt, lines 551–558](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L551-L558) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L546-L649 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `FunctionalInequalities.Analysis.le_det_hessianMatrix_of_upper_touch`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open FunctionalInequalities.Probability.Stein
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.le_det_hessianMatrix_of_upper_touch_readable {n : ℕ} {u f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    f x₀ ≤ (hessianMatrix ψ x₀).det := by sorry
