-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test_readable
-- name    : FunctionalInequalities.Analysis.integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:45.910985+00:00
-- url     : https://prove2.me/theorems/68f53a73-98d0-4677-9ebd-c4a0016296fd
-- title:
--   Compact Flux Identity for Globally Bounded Weak Tests
-- statement:
--   This is a weak integration-by-parts extension for compactly supported fluxes.
--
--   Let $J_i$ and $F$ be compactly supported, with each $J_i$ compact-locally in $L^2$ and $F$ locally integrable. Assume every compactly supported $C^1$ function $\psi$ satisfies
--
--   $$
--   \int\sum_iJ_i\,\partial_i\psi\,dx=-\int F\psi\,dx.
--   $$
--
--   Let $\eta$ be locally integrable and globally bounded by $C$. Suppose $a_i$ is a weak derivative of $\eta$ in the $i$-th coordinate direction and is compact-locally in $L^2$ for every compact set. Then each $J_i a_i$ and $F\eta$ is integrable, and
--
--   $$
--   \int\sum_iJ_i(x)a_i(x)\,dx=-\int F(x)\eta(x)\,dx.
--   $$
--
--   The compact support of both the flux components and the forcing replaces compact support of the test function.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test {n : ℕ}
--       {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
--       {F η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
--       (hJ : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
--       (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hJc : ∀ i : Fin n, HasCompactSupport (J i)) (hFc : HasCompactSupport F)
--       (hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
--         ContDiff ℝ 1 ψ → HasCompactSupport ψ →
--         (∫ x, ∑ i : Fin n, J i x * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i)
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--         -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
--       (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hbound : ∀ x, ‖η x‖ ≤ C)
--       (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
--       (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
--       (∀ i : Fin n, Integrable (fun x => J i x * a i x)
--         (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
--       Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--       (∫ x, ∑ i : Fin n, J i x * a i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--         -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`HasWeakDerivAlong.compact_mul_data`](https://prove2.me/theorems/14d1dc0b-7afe-403f-ae05-0178b771addc), [`integral_flux_eq_neg_forcing_of_bounded_weak_test`](https://prove2.me/theorems/a62894bf-0470-4e04-8a24-6f8073da24d8).
--
--   Previous: [`HasWeakDerivAlong.compact_mul_data`](https://prove2.me/theorems/14d1dc0b-7afe-403f-ae05-0178b771addc) · Next: [`integral_eq_zero_of_integrable_weak_derivative`](https://prove2.me/theorems/4bbf5126-d256-459b-9474-606b9a141762).
--
--   [Source excerpt, lines 1398–1419](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1398-L1419) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1395-L1477 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory Filter Set Metric

theorem FunctionalInequalities.Analysis.integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test_readable {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hJ : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hJc : ∀ i : Fin n, HasCompactSupport (J i)) (hFc : HasCompactSupport F)
    (hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, ∑ i : Fin n, J i x * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    (∀ i : Fin n, Integrable (fun x => J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ i : Fin n, J i x * a i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
