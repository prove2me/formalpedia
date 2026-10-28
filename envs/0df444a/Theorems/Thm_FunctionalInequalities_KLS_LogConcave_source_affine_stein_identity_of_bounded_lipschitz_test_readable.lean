-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_source_affine_stein_identity_of_bounded_lipschitz_test_readable
-- name    : FunctionalInequalities.KLS.LogConcave.source_affine_stein_identity_of_bounded_lipschitz_test_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:20.147991+00:00
-- url     : https://prove2.me/theorems/e5b3ff9c-092e-463b-98ea-ed142c530c1b
-- title:
--   Affine Source Stein Identity
-- statement:
--   This statement gives the affine version of the source Stein identity.
--
--   Let $n\in\mathbb N$. Let $u,h:\mathbb R^n\to\mathbb R$ be $C^1$, with $u$ and $∇u$ globally Lipschitz and $\int e^{-u}=1$. Let $h$ be globally Lipschitz and bounded by $C$. For a continuous linear map $S$, and vectors $z,v\in\mathbb R^n$, both functions below are integrable under $ν=\operatorname{volume}.\operatorname{tilted}(-u)$, and
--
--   $$
--   \int \langle S∇u(y),v\rangle h(S∇u(y)+z)\,dν(y)
--   =
--   \int \left\langle S^*v,\operatorname{action}\!\left(\nabla^2u(y),S^*∇h(S∇u(y)+z)\right)\right\rangle dν(y).
--   $$
--
--   This identity is the affine source component used in the Gaussian product coupling.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 600000 in
--   theorem source_affine_stein_identity_of_bounded_lipschitz_test {n : ℕ}
--       {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal}
--       (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
--       (hG : LipschitzWith G (gradient u))
--       (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
--       (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
--       (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
--       (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
--       (z v : EuclideanSpace ℝ (Fin n)) :
--       Integrable (fun y => ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z))
--         ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
--       Integrable (fun y => ⟪S.adjoint v,
--         action (hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫)
--         ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
--       (∫ y, ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z)
--         ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
--         ∫ y, ⟪S.adjoint v,
--           action (hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫
--           ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HessianStein`](https://prove2.me/theorems/72cb6534-e95d-45a6-ad0a-93acef4b771e).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e).
--
--   Supporting theorems: [`source_stein_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/abe8f632-2fbe-4518-9208-6c81be572011).
--
--   Previous: [`source_stein_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/abe8f632-2fbe-4518-9208-6c81be572011).
--
--   [Source excerpt, lines 352–371](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HessianStein.lean#L352-L371) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HessianStein.lean#L352-L385 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HessianStein`, declaration `FunctionalInequalities.KLS.LogConcave.source_affine_stein_identity_of_bounded_lipschitz_test`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HessianStein

open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
set_option maxHeartbeats 600000

theorem FunctionalInequalities.KLS.LogConcave.source_affine_stein_identity_of_bounded_lipschitz_test_readable {n : ℕ}
    {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
    (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (z v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    Integrable (fun y => ⟪S.adjoint v,
      action (hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    (∫ y, ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
      ∫ y, ⟪S.adjoint v,
        action (hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by sorry
