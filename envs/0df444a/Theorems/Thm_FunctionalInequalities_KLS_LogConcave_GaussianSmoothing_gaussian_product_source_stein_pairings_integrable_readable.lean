-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussian_product_source_stein_pairings_integrable_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_source_stein_pairings_integrable_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:35.715989+00:00
-- url     : https://prove2.me/theorems/baf328a1-6649-44a0-8197-8f43bfab886c
-- title:
--   Integrability of Source and Noise Stein Pairings
-- statement:
--   This statement establishes the integrability hypotheses for the Gaussian product coupling.
--
--   Let $n\in\mathbb N$. Let $u,h:\mathbb R^n\to\mathbb R$ be $C^1$ functions, with $u$ and $∇u$ globally Lipschitz, $∇u$ having Lipschitz constant `G`, and with
--
--   $$
--   \int e^{-u(y)}\,dy=1.
--   $$
--
--   Let $h$ be globally Lipschitz and bounded by $C$, let $S$ be continuous linear, let $v\in\mathbb R^n$, and let $s>0$. On the product measure
--
--   $$
--   P=\bigl(\operatorname{volume}.\operatorname{tilted}(-u)\bigr)\otimes\gamma_s,
--   $$
--
--   with $Z(y,z)=S(∇u(y))+z$ and $F(y,z)=S(\operatorname{action}(\nabla^2u(y),S^*v))$, the theorem asserts that $Z$, $F$, $∇h\circ Z$ belong to `MemLp · 2 P`, and that the source pairing, noise pairing, Hessian pairing, and derivative pairing appearing in the product Stein identity are all integrable under $P$.
--
--   This is a technical integrability package supporting the subsequent product Stein identity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 800000 in
--   theorem gaussian_product_source_stein_pairings_integrable {n : ℕ}
--       {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal}
--       (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
--       (hG : LipschitzWith G (gradient u))
--       (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
--       (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
--       (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
--       (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
--       (v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
--       let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
--         (gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
--       let Z := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => S (gradient u p.1) + p.2
--       let F := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
--         S (action (hessianMatrix u p.1) (S.adjoint v))
--       MemLp Z 2 P ∧ MemLp F 2 P ∧ MemLp (fun p => gradient h (Z p)) 2 P ∧
--       Integrable (fun p => ⟪S (gradient u p.1),v⟫ * h (Z p)) P ∧
--       Integrable (fun p => ⟪p.2,v⟫ * h (Z p)) P ∧
--       Integrable (fun p => ⟪S.adjoint v,action (hessianMatrix u p.1) (S.adjoint (gradient h (Z p)))⟫) P ∧
--       Integrable (fun p => fderiv ℝ h (Z p) v) P
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling`](https://prove2.me/theorems/ec60ae0c-90e6-43f3-859c-75d3c6dd9a5f).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575), [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e).
--
--   Supporting theorems: [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e), [`norm_hessianMatrix_entry_le_of_lipschitz_gradient`](https://prove2.me/theorems/c390fe75-eaf1-41ee-934b-fddb8427fab6).
--
--   Next: [`gaussian_product_source_stein_identity`](https://prove2.me/theorems/23d8691b-4721-4fa3-a71c-9a8a4ef02ab4).
--
--   [Source excerpt, lines 36–55](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling.lean#L36-L55) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling.lean#L36-L110 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.ProductCoupling`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_source_stein_pairings_integrable`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_ProductCoupling

open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
set_option maxHeartbeats 800000

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_source_stein_pairings_integrable_readable {n : ℕ}
    {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
    (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
    let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
      (gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
    let Z := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => S (gradient u p.1) + p.2
    let F := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      S (action (hessianMatrix u p.1) (S.adjoint v))
    MemLp Z 2 P ∧ MemLp F 2 P ∧ MemLp (fun p => gradient h (Z p)) 2 P ∧
    Integrable (fun p => ⟪S (gradient u p.1),v⟫ * h (Z p)) P ∧
    Integrable (fun p => ⟪p.2,v⟫ * h (Z p)) P ∧
    Integrable (fun p => ⟪S.adjoint v,action (hessianMatrix u p.1) (S.adjoint (gradient h (Z p)))⟫) P ∧
    Integrable (fun p => fderiv ℝ h (Z p) v) P := by sorry
