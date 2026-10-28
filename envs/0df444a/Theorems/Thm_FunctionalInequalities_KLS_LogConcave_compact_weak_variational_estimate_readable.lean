-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_compact_weak_variational_estimate_readable
-- name    : FunctionalInequalities.KLS.LogConcave.compact_weak_variational_estimate_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:15.90766+00:00
-- url     : https://prove2.me/theorems/a0f061ff-8443-47ab-968d-50cf20a09f59
-- title:
--   Weak Compact Variational Estimate
-- statement:
--   This formalizes part of Lemma A.6 of Letwin (arXiv:2607.24164v1), cited as “Brascamp–Lieb for $\nu$.”
--
--   Work on $E=\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$. Let $\nu$ be a probability measure and $U,\eta,v:E\to\mathbb R$. Assume:
--
--   1. $\nu=e^{-U}\,dx$ in the Lean tilted-measure sense;
--   2. $U$ is $C^1$, globally Lipschitz, has Lipschitz gradient, and $\int e^{-U}\,dx=1$;
--   3. $\nabla^2U(x)$ is positive definite for almost every $x$;
--   4. $a_i:E\to\mathbb R$ are weak coordinate derivatives of the locally integrable, globally bounded function $\eta$, with $\|\eta(x)\|\le C$;
--   5. each $a_i$ is locally $L^2$ on compact sets;
--   6. the inverse-Hessian energy
--   $$\int_E\sum_{i,j}a_i(x)\bigl((\nabla^2U(x))^{-1}\bigr)_{ij}a_j(x)\,d\nu(x)$$
--    is integrable;
--   7. $v$ is smooth of class $C^\infty$ and has compact support.
--
--   Then both $\eta(-\mathcal L_Uv)$ and $(\mathcal L_Uv)^2$ are integrable under $\nu$, and
--
--   $$2\int_E\eta(x)(-\mathcal L_Uv(x))\,d\nu(x)-\int_E(\mathcal L_Uv(x))^2\,d\nu(x)
--   \le \int_E a(x)^\mathsf T(\nabla^2U(x))^{-1}a(x)\,d\nu(x).$$
--
--   The declaration is a weak, finite-energy variational estimate for compactly supported smooth test functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem compact_weak_variational_estimate {n : ℕ}
--       {nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
--       {U eta v : EuclideanSpace ℝ (Fin n) → ℝ}
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
--         ((hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))) (nu : Measure (EuclideanSpace ℝ (Fin n))))
--       (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
--       Integrable (fun x => eta x * (-weightedLaplacian U v x)) (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
--       Integrable (fun x => weightedLaplacian U v x ^ 2) (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
--       2 * (∫ x, eta x * (-weightedLaplacian U v x) ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) -
--         (∫ x, weightedLaplacian U v x ^ 2 ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) ≤
--           ∫ x, (fun i => a i x) ⬝ᵥ ((hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))
--             ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeakBrascampLieb`](https://prove2.me/theorems/4d759700-9cad-4791-aded-7197e3d56cfa).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`compact_ordinary_diffusion_coercivity_of_lipschitz_gradient`](https://prove2.me/theorems/2333fc8d-b8d0-4b91-abd1-9ba2b3b18409), [`integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one`](https://prove2.me/theorems/6f50482d-1332-4259-9737-8faba5cabf29), [`inverse_quadratic_young`](https://prove2.me/theorems/88b8a40a-52a8-4842-a7d8-a36165a50c94).
--
--   Next: [`scalar_brascamp_lieb_weak_finite_energy`](https://prove2.me/theorems/e67ea706-0bd9-4ce6-a4b9-8b19dd948f1a).
--
--   [Source excerpt, lines 43–66](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeakBrascampLieb.lean#L43-L66) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.6. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeakBrascampLieb.lean#L40-L112 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeakBrascampLieb`, declaration `FunctionalInequalities.KLS.LogConcave.compact_weak_variational_estimate`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeakBrascampLieb

open MeasureTheory Filter Topology Set InnerProductSpace Matrix
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
set_option maxHeartbeats 2000000

theorem FunctionalInequalities.KLS.LogConcave.compact_weak_variational_estimate_readable {n : ℕ}
    {nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {U eta v : EuclideanSpace ℝ (Fin n) → ℝ}
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
      ((hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))) (nu : Measure (EuclideanSpace ℝ (Fin n))))
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    Integrable (fun x => eta x * (-weightedLaplacian U v x)) (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => weightedLaplacian U v x ^ 2) (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
    2 * (∫ x, eta x * (-weightedLaplacian U v x) ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) -
      (∫ x, weightedLaplacian U v x ^ 2 ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, (fun i => a i x) ⬝ᵥ ((hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))
          ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
