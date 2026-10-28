-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_penalized_maximum_with_comparison_readable
-- name    : FunctionalInequalities.Analysis.exists_penalized_maximum_with_comparison_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:39.991489+00:00
-- url     : https://prove2.me/theorems/511a8bb6-640f-477b-98fa-7c8e07f3450e
-- title:
--   Penalized Maximum and Density Comparison
-- statement:
--   This is a weak-route supporting theorem for Letwin’s second-difference argument.
--
--   Let $u,F:\mathbb R^n\to\mathbb R$. Assume: $u$ is convex, globally Lipschitz, and has compact sublevel sets; $F$ is continuous; and for every open $G$, the Alexandrov identity
--   $$\operatorname{vol}(\partial u(G))=\int_G e^{F(x)}\,dx$$
--   holds. Let $u_k\in C^2$ and $F_k$ satisfy uniform approximation $|u_k-u|\le\delta_k$ with $\delta_k\to0$, local uniform convergence $F_k\to F$, positive-definite $\nabla^2u_k$, and $F_k\le\log\det\nabla^2u_k$. For every $h\in\mathbb R^n$ and $\eta>0$, there exists $x_0$ such that $\Delta_h^2u(x_0)-\eta u(x_0)$ is maximal and
--
--   $$F(x_0+h)+F(x_0-h)-2F(x_0)\le\eta n.$$
--
--   This is an auxiliary existence and comparison result, not a dimension-free bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_penalized_maximum_with_comparison {n : ℕ} {u F : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hconv : ConvexOn ℝ univ u) {L : NNReal} (hLip : LipschitzWith L u)
--       (hcoer : ∀ R : ℝ, IsCompact {x | u x ≤ R}) (hF : Continuous F)
--       (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
--         (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
--           ∫⁻ x in G, ENNReal.ofReal (Real.exp (F x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--       {uk Fk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} (huk : ∀ k, ContDiff ℝ 2 (uk k))
--       {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hclose : ∀ k x, |uk k x - u x| ≤ δ k)
--       (hFk : TendstoLocallyUniformly Fk F atTop)
--       (hpos : ∀ k x, (hessianMatrix (uk k) x).PosDef)
--       (hlog : ∀ k x, Fk k x ≤ Real.log (hessianMatrix (uk k) x).det)
--       (h : EuclideanSpace ℝ (Fin n)) {η : ℝ} (hη : 0 < η) :
--       ∃ x₀ : EuclideanSpace ℝ (Fin n),
--         (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
--           u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
--         F (x₀ + h) + F (x₀ - h) - 2 * F x₀ ≤ η * n
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`det_hessianMatrix_le_of_lower_touch`](https://prove2.me/theorems/0a6a663c-c593-49af-8752-569576e141d5), [`forall_posDef_add_log_det_le_trace_iff`](https://prove2.me/theorems/99f67c0b-fea3-4671-8e5b-e62a896aa733).
--
--   Previous: [`ae_exists_quadraticAt_expansion`](https://prove2.me/theorems/995efd14-b691-40e5-adc5-c0effdf385d3) · Next: [`ae_hessian_increment_le_generator`](https://prove2.me/theorems/8a32f083-457a-427c-a413-4a9bda9a98fb).
--
--   [Source excerpt, lines 1707–1722](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1707-L1722) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1701-L1795 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `FunctionalInequalities.Analysis.exists_penalized_maximum_with_comparison`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open FunctionalInequalities.Probability.Stein
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.exists_penalized_maximum_with_comparison_readable {n : ℕ} {u F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {L : NNReal} (hLip : LipschitzWith L u)
    (hcoer : ∀ R : ℝ, IsCompact {x | u x ≤ R}) (hF : Continuous F)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (Real.exp (F x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {uk Fk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} (huk : ∀ k, ContDiff ℝ 2 (uk k))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hclose : ∀ k x, |uk k x - u x| ≤ δ k)
    (hFk : TendstoLocallyUniformly Fk F atTop)
    (hpos : ∀ k x, (hessianMatrix (uk k) x).PosDef)
    (hlog : ∀ k x, Fk k x ≤ Real.log (hessianMatrix (uk k) x).det)
    (h : EuclideanSpace ℝ (Fin n)) {η : ℝ} (hη : 0 < η) :
    ∃ x₀ : EuclideanSpace ℝ (Fin n),
      (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
        u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
      F (x₀ + h) + F (x₀ - h) - 2 * F x₀ ≤ η * n := by sorry
