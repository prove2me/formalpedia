-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_trace_quadratic_le_two_mul_trace_sq_readable
-- name    : FunctionalInequalities.KLS.LogConcave.integral_trace_quadratic_le_two_mul_trace_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:22.539953+00:00
-- url     : https://prove2.me/theorems/0915019c-ff4d-443b-bb7e-f4eeece90338
-- title:
--   Weak Hessian Trace Bound
-- statement:
--   This formalizes the weak $C^{1,1}$ form of Theorem 2.5 of Letwin (arXiv:2607.24164v1), cited as “Key moment-map Hessian bound.”
--
--   Let $\nu$ be a probability measure on $E=\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$ with $\nu=e^{-U}\,dx$, where $U$ is convex, $C^1$, globally Lipschitz, has Lipschitz gradient, and satisfies $\int e^{-U}\,dx=1$. Assume $\nabla^2U$ is positive definite almost everywhere. Let $T_k$ be a weak derivative tensor for the Hessian entries, locally $L^2$ on compact sets, and assume compact-local $L^\infty$ integrability of the inverse Hessian entries. Assume every Hessian entry is $\nu$-integrable with mean equal to the identity matrix. For a positive-semidefinite matrix $B$, assume the corresponding inverse-Hessian tensor energy is integrable and satisfies the half-energy bound
--
--   $$\int \sum_{k,l}(\nabla^2U)^{-1}_{kl}\,\operatorname{tr}(BT_kBT_l)\,d\nu
--   \le \frac12\int\operatorname{tr}(B\nabla^2U B\nabla^2U)\,d\nu.$$
--
--   Then $\operatorname{tr}(B\nabla^2U B\nabla^2U)$ is integrable and
--
--   $$\int\operatorname{tr}(B\nabla^2U B\nabla^2U)\,d\nu\le 2\operatorname{tr}(B^2).$$
--
--   The statement is a weak Hessian-trace estimate with all differentiability and local integrability hypotheses explicit.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--           (1 : Matrix (Fin n) (Fin n) ℝ) i j)
--       (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef)
--       (hD : Integrable (fun x => ∑ k : Fin n, ∑ l : Fin n, (hessianMatrix U x)⁻¹ k l *
--         (B * T x k * B * T x l).trace) (nu : Measure (EuclideanSpace ℝ (Fin n))))
--       (hhalf : (∫ x, (∑ k : Fin n, ∑ l : Fin n, (hessianMatrix U x)⁻¹ k l *
--         (B * T x k * B * T x l).trace) ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) ≤
--         (1 / 2 : ℝ) * ∫ x, (B * hessianMatrix U x * B * hessianMatrix U x).trace
--           ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) :
--       Integrable (fun x => (B * hessianMatrix U x * B * hessianMatrix U x).trace)
--         (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
--       (∫ x, (B * hessianMatrix U x * B * hessianMatrix U x).trace
--         ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) ≤ 2 * (B * B).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HessianTrace`](https://prove2.me/theorems/a007d6bd-8267-4526-a1ec-a10003542850).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Selected supporting theorems: [`ae_weak_third_derivative_symm`](https://prove2.me/theorems/236baf49-0092-428b-8c19-9934eff0cfd3), [`bounded_weak_matrix_product_entry`](https://prove2.me/theorems/3c19e2fb-eb53-4358-81de-489fd6539c03), [`sum_matrix_product_entry_mul_eq_trace`](https://prove2.me/theorems/3c931abe-bff8-4022-a4df-7236818e79cd), [`sum_matrix_product_entry_quadratic_eq_trace`](https://prove2.me/theorems/d887a248-417a-44cd-bedd-9dbc45f1c640), [`isBorellDensity_of_eq_tilted`](https://prove2.me/theorems/0d7194a7-857d-46cc-b91c-8366be9b61de).
--
--   [Source excerpt, lines 133–144](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HessianTrace.lean#L133-L144) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HessianTrace.lean#L108-L288 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HessianTrace`, declaration `FunctionalInequalities.KLS.LogConcave.integral_trace_quadratic_le_two_mul_trace_sq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HessianTrace

open MeasureTheory Matrix
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 4000000

theorem FunctionalInequalities.KLS.LogConcave.integral_trace_quadratic_le_two_mul_trace_sq_readable {n : ℕ}
    {nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {U : EuclideanSpace ℝ (Fin n) → ℝ}
    (hnuU : (nu : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))
    (hconv : ConvexOn ℝ Set.univ U) (hU : ContDiff ℝ 1 U)
    {G : NNReal} (hG : LipschitzWith G (gradient U)) {L : NNReal} (hL : LipschitzWith L U)
    (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix U x).PosDef)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix U x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
        MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K))
    (hR : ∀ i j : Fin n, ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MemLp (fun x => (hessianMatrix U x)⁻¹ i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K))
    (hmean : ∀ i j : Fin n,
      Integrable (fun x => hessianMatrix U x i j) (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, hessianMatrix U x i j ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) =
        (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef)
    (hD : Integrable (fun x => ∑ k : Fin n, ∑ l : Fin n, (hessianMatrix U x)⁻¹ k l *
      (B * T x k * B * T x l).trace) (nu : Measure (EuclideanSpace ℝ (Fin n))))
    (hhalf : (∫ x, (∑ k : Fin n, ∑ l : Fin n, (hessianMatrix U x)⁻¹ k l *
      (B * T x k * B * T x l).trace) ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      (1 / 2 : ℝ) * ∫ x, (B * hessianMatrix U x * B * hessianMatrix U x).trace
        ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) :
    Integrable (fun x => (B * hessianMatrix U x * B * hessianMatrix U x).trace)
      (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, (B * hessianMatrix U x * B * hessianMatrix U x).trace
      ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) ≤ 2 * (B * B).trace := by sorry
