-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_posDef_and_det_eq_of_quadratic_expansion_readable
-- name    : FunctionalInequalities.Analysis.posDef_and_det_eq_of_quadratic_expansion_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:59.635289+00:00
-- url     : https://prove2.me/theorems/fdeb8c35-d7cf-4a28-9642-da29fd09799b
-- title:
--   Positive Hessian and Determinant from Quadratic Expansion
-- statement:
--   Let $u,f:\mathbb R^n\to\mathbb R$, let $\Omega$ be open, and assume $u$ is convex and satisfies the Alexandrov identity
--   $$\operatorname{vol}(\partial u(G))=\int_G\operatorname{ofReal}(f(x))\,dx$$
--   for every open $G\subseteq\Omega$. If $x_0\in\Omega$, $f$ is continuous at $x_0$ with $f(x_0)>0$, and there are a Hermitian matrix $B$ and vector $g$ such that, for every $\varepsilon>0$,
--   $$|u(x)-\operatorname{quadraticAt}(B,x_0,g,u(x_0))(x)|\le\varepsilon\|x-x_0\|^2$$
--   near $x_0$, then
--
--   $$B\succ0\qquad\text{and}\qquad\det B=f(x_0).$$
--
--   This is a pointwise Monge–Ampère identification at second-order differentiability points.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem posDef_and_det_eq_of_quadratic_expansion {n : ℕ} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
--       (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
--         (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
--           ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--       {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀) (hfpos : 0 < f x₀)
--       {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) {g : EuclideanSpace ℝ (Fin n)}
--       (hexp : ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, |u x - quadraticAt B x₀ g (u x₀) x| ≤ ε * ‖x - x₀‖ ^ 2) :
--       B.PosDef ∧ B.det = f x₀
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905), [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`det_hessianMatrix_le_of_lower_touch`](https://prove2.me/theorems/0a6a663c-c593-49af-8752-569576e141d5), [`hessianMatrix_quadraticAt`](https://prove2.me/theorems/facc6c9b-040a-4551-a141-72b34dae970f), [`le_det_hessianMatrix_of_upper_touch`](https://prove2.me/theorems/6c79ec26-adc7-48d0-89d1-5a5ef657b31d), [`posSemidef_hessianMatrix_of_upper_touch`](https://prove2.me/theorems/c0934c18-f16d-42fc-a97b-28fa4ccb6c6d).
--
--   Previous: [`hessianMatrix_quadraticAt`](https://prove2.me/theorems/facc6c9b-040a-4551-a141-72b34dae970f) · Next: [`expansion_secondDifference`](https://prove2.me/theorems/546aab2f-04b5-4802-87d1-3ee07a4c5efe).
--
--   [Source excerpt, lines 912–920](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L912-L920) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L908-L976 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `FunctionalInequalities.Analysis.posDef_and_det_eq_of_quadratic_expansion`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology

theorem FunctionalInequalities.Analysis.posDef_and_det_eq_of_quadratic_expansion_readable {n : ℕ} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀) (hfpos : 0 < f x₀)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) {g : EuclideanSpace ℝ (Fin n)}
    (hexp : ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, |u x - quadraticAt B x₀ g (u x₀) x| ≤ ε * ‖x - x₀‖ ^ 2) :
    B.PosDef ∧ B.det = f x₀ := by sorry
