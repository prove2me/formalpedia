-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_flux_eq_neg_forcing_of_bounded_weak_test_readable
-- name    : FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:43.604835+00:00
-- url     : https://prove2.me/theorems/a62894bf-0470-4e04-8a24-6f8073da24d8
-- title:
--   Bounded Weak-Test Extension of Flux Integration by Parts
-- statement:
--   This is a finite-dimensional weak integration-by-parts extension.
--
--   Let $J_i$ be compact-locally in $L^2$, let $F$ be locally integrable, and suppose every compactly supported $C^1$ test $\psi$ satisfies
--
--   $$
--   \int\sum_iJ_i\,\partial_i\psi\,dx=-\int F\psi\,dx.
--   $$
--
--   Let $\eta$ be locally integrable, bounded by a constant $C$ in norm, and compactly supported. Suppose $a_i$ is a weak derivative of $\eta$ in the $i$-th coordinate direction, each $a_i$ is compactly supported, and each $a_i$ belongs globally to $L^2$. Then all products $J_i a_i$ and $F\eta$ are integrable and
--
--   $$
--   \int\sum_iJ_i(x)a_i(x)\,dx
--   =-\int F(x)\eta(x)\,dx.
--   $$
--
--   This theorem extends a compact $C^1$ test identity to bounded compactly supported weak tests; it includes the case $n=0$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_flux_eq_neg_forcing_of_bounded_weak_test {n : ℕ}
--       {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
--       {F η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
--       (hJ : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
--       (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
--         ContDiff ℝ 1 ψ → HasCompactSupport ψ →
--         (∫ x, ∑ i : Fin n, J i x * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i)
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--         -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
--       (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
--       (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
--       (hac : ∀ i : Fin n, HasCompactSupport (a i))
--       (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
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
--   Supporting theorems: [`compact_bounded_test_domination`](https://prove2.me/theorems/598f7c40-05a7-49e8-94fe-b29d9620425b), [`exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset`](https://prove2.me/theorems/edd33fcd-2ede-42b0-a5c4-34bd95e40e19).
--
--   Previous: [`compact_bounded_test_domination`](https://prove2.me/theorems/598f7c40-05a7-49e8-94fe-b29d9620425b) · Next: [`HasWeakDerivAlong.compact_mul_data`](https://prove2.me/theorems/14d1dc0b-7afe-403f-ae05-0178b771addc).
--
--   [Source excerpt, lines 1272–1292](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1272-L1292) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1268-L1304 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory Filter Set

theorem FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test_readable {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hJ : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, ∑ i : Fin n, J i x * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∀ i : Fin n, Integrable (fun x => J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ i : Fin n, J i x * a i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
