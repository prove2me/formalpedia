-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_scalar_brascamp_lieb_weak_finite_energy_readable
-- name    : FunctionalInequalities.KLS.LogConcave.scalar_brascamp_lieb_weak_finite_energy_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:43.983967+00:00
-- url     : https://prove2.me/theorems/e67ea706-0bd9-4ce6-a4b9-8b19dd948f1a
-- title:
--   Weak Finite-Energy Scalar Brascamp–Lieb Inequality
-- statement:
--   This formalizes the scalar finite-energy form of Lemma A.6 of Letwin (arXiv:2607.24164v1), cited as “Brascamp–Lieb for $\nu$.”
--
--   Let $\nu$ be a log-concave probability measure on $E=\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$, with $\nu=e^{-U}\,dx$ in the tilted-measure sense. Assume that $U$ is $C^1$, globally Lipschitz, has Lipschitz gradient, and satisfies $\int e^{-U}\,dx=1$; assume also that $\nabla^2U(x)$ is positive definite almost everywhere. Let $\eta:E\to\mathbb R$ be locally integrable and globally bounded by $C$, and let $a_i$ be its weak derivatives along the coordinate basis, locally in $L^2$ on compact sets. Finally assume the inverse-Hessian energy is integrable. Then
--
--   $$\operatorname{Var}_{\nu}(\eta)\le \int_E a(x)^\mathsf T(\nabla^2U(x))^{-1}a(x)\,d\nu(x).$$
--
--   The inequality is stated for weakly differentiable bounded tests and explicitly requires finite inverse-Hessian energy; it does not assert a bound for arbitrary unbounded or infinite-energy tests.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem scalar_brascamp_lieb_weak_finite_energy {n : ℕ}
--       {nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hnu : KLS.LogConcave nu)
--       {U eta : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hnuU : (nu : Measure (EuclideanSpace ℝ (Fin n))) =
--         (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))
--       (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U))
--       {L : NNReal} (hL : LipschitzWith L U)
--       (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
--       (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix U x).PosDef)
--       (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ)
--       (heta : LocallyIntegrable eta (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hbound : ∀ x, ‖eta x‖ ≤ C)
--       (hweak : ∀ i : Fin n, HasWeakDerivAlong eta (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
--       (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
--       (henergy : Integrable (fun x => (fun i => a i x) ⬝ᵥ
--         ((hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))) (nu : Measure (EuclideanSpace ℝ (Fin n)))) :
--       ProbabilityTheory.variance eta (nu : Measure (EuclideanSpace ℝ (Fin n))) ≤
--         ∫ x, (fun i => a i x) ⬝ᵥ ((hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))
--           ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeakBrascampLieb`](https://prove2.me/theorems/4d759700-9cad-4791-aded-7197e3d56cfa).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`centered_mem_closure_compactSmoothDiffusionImage`](https://prove2.me/theorems/cc2ca884-a315-433e-8321-8e49b01e29b4), [`compact_weak_variational_estimate`](https://prove2.me/theorems/a0f061ff-8443-47ab-968d-50cf20a09f59), [`inner_center_left_of_mean_zero`](https://prove2.me/theorems/eeca0bb8-9f32-4e5c-ba1e-1f7ba9ea09b0), [`norm_sq_le_of_mem_closure_quadratic_bound`](https://prove2.me/theorems/db1af422-d999-42df-956f-acb4a17024e8).
--
--   Previous: [`compact_weak_variational_estimate`](https://prove2.me/theorems/a0f061ff-8443-47ab-968d-50cf20a09f59).
--
--   [Source excerpt, lines 119–138](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeakBrascampLieb.lean#L119-L138) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.6. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeakBrascampLieb.lean#L114-L173 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeakBrascampLieb`, declaration `FunctionalInequalities.KLS.LogConcave.scalar_brascamp_lieb_weak_finite_energy`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeakBrascampLieb

open MeasureTheory Filter Topology Set InnerProductSpace Matrix
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 2000000

theorem FunctionalInequalities.KLS.LogConcave.scalar_brascamp_lieb_weak_finite_energy_readable {n : ℕ}
    {nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hnu : KLS.LogConcave nu)
    {U eta : EuclideanSpace ℝ (Fin n) → ℝ}
    (hnuU : (nu : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))
    (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U))
    {L : NNReal} (hL : LipschitzWith L U)
    (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix U x).PosDef)
    (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ)
    (heta : LocallyIntegrable eta (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong eta (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (henergy : Integrable (fun x => (fun i => a i x) ⬝ᵥ
      ((hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))) (nu : Measure (EuclideanSpace ℝ (Fin n)))) :
    ProbabilityTheory.variance eta (nu : Measure (EuclideanSpace ℝ (Fin n))) ≤
      ∫ x, (fun i => a i x) ⬝ᵥ ((hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))
        ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
