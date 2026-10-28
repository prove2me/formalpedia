-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one_readable
-- name    : FunctionalInequalities.Analysis.integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:57.282999+00:00
-- url     : https://prove2.me/theorems/6f50482d-1332-4259-9737-8faba5cabf29
-- title:
--   Weak Integration By Parts For The Weighted Laplacian
-- statement:
--   This formalizes part of Lemma A.6 of Letwin (arXiv:2607.24164v1), whose reviewed paper statement is the Brascamp–Lieb inequality for the tilted law.
--
--   Let n be a natural number and work on $E=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$. Let U be C¹, let v be smooth, and assume v has compact support. Normalize the exponential weight by
--
--   $$\int_E e^{-U(x)}\,dx=1.$$
--
--   Let η be locally integrable and globally bounded by C in norm. For each coordinate i, suppose η has weak derivative aᵢ along the i-th Euclidean basis direction, and suppose every aᵢ belongs locally to $L^2$ on compact sets. Then both functions
--
--   $$x\mapsto \eta(x)\,\mathcal L_Uv(x)$$
--
--   and
--
--   $$x\mapsto\sum_i a_i(x)\,D_{e_i}v(x)$$
--
--   are integrable with respect to the tilted measure $d\nu=e^{-U}dx$, and
--
--   $$\int \eta\,\mathcal L_Uv\,d\nu=-\int\sum_i a_iD_{e_i}v\,d\nu.$$
--
--   Here $\mathcal L_Uv=\Delta v-\langle\nabla U,\nabla v\rangle$ is the ordinary weighted Laplacian.
--
--   The declaration is a rough integration-by-parts tool for compactly supported tests and weakly differentiable bounded multipliers.
--
--   **Formalization Note** The conclusion is stated for all n, including n=0; the tilted measure is formed from volume measure and the function −U.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one {n : ℕ}
--       {U v eta : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hU : ContDiff ℝ 1 U) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
--       (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
--       (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ)
--       (heta : LocallyIntegrable eta (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hbound : ∀ x, ‖eta x‖ ≤ C)
--       (hweak : ∀ i : Fin n, HasWeakDerivAlong eta (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
--       (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
--       Integrable (fun x => eta x * weightedLaplacian U v x)
--         ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
--       Integrable (fun x => ∑ i : Fin n, a i x *
--         fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i))
--         ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
--       (∫ x, eta x * weightedLaplacian U v x
--         ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) =
--         -(∫ x, (∑ i : Fin n, a i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i))
--           ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/WeakLaplacian`](https://prove2.me/theorems/db3f6cfa-f4e0-461a-859a-e5e7e56c5272).
--
--   Definition modules: [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test`](https://prove2.me/theorems/68f53a73-98d0-4677-9ebd-c4a0016296fd).
--
--   [Source excerpt, lines 25–43](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakLaplacian.lean#L25-L43) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.6. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakLaplacian.lean#L21-L129 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakLaplacian`, declaration `FunctionalInequalities.Analysis.integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakLaplacian

open MeasureTheory Filter Set Metric
open scoped ContDiff Topology RealInnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.Analysis.integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one_readable {n : ℕ}
    {U v eta : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : ContDiff ℝ 1 U) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ)
    (heta : LocallyIntegrable eta (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong eta (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    Integrable (fun x => eta x * weightedLaplacian U v x)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    Integrable (fun x => ∑ i : Fin n, a i x *
      fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    (∫ x, eta x * weightedLaplacian U v x
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) =
      -(∫ x, (∑ i : Fin n, a i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) := by sorry
