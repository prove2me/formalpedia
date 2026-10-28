-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_trace_contraction_of_coordinate_pairings_readable
-- name    : FunctionalInequalities.Analysis.integral_trace_contraction_of_coordinate_pairings_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:06.894977+00:00
-- url     : https://prove2.me/theorems/95e16cb2-bd29-4841-b725-9353894707a0
-- title:
--   Coordinate Trace Contraction Identity
-- statement:
--   This auxiliary statement performs a finite trace contraction of coordinatewise integral identities.
--
--   Let d,n,m be natural numbers. On $E=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} d)$, let B be an n-by-n matrix; let H and E be matrix fields; let T and J be m-indexed matrix fields; let ρ and ψ be scalar fields; and let dψₐ be scalar coordinate derivatives. Assume the five families of coordinate expressions appearing in the theorem are integrable, including the pairings involving J, T, H, E, B, ρ, ψ, and dψ. Assume also that for every l,k,i,j,
--
--   $$\int ρ\sum_a J_{a,ij}\bigl(ψT_{a,lk}+dψ_aH_{lk}\bigr)\,d\mu
--   =-\int ρE_{ij}ψH_{lk}\,d\mu.$$
--
--   Then the contracted flux identity holds:
--
--   $$\int ρ\sum_a 2\operatorname{tr}(BHBJ_a)\,dψ_a\,d\mu
--   =-\int ρ\left(2\operatorname{tr}(BHBE)+\sum_a2\operatorname{tr}(BT_aBJ_a)\right)ψ\,d\mu.$$
--
--   This is a finite-sum and trace-algebra support lemma used by the public weak trace contraction theorem.
--
--   **Formalization Note** All integrals are with respect to the explicitly supplied measure μ; no analytic interpretation of the fields as Hessians or derivatives is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem integral_trace_contraction_of_coordinate_pairings {d n m : ℕ}
--       (mu : Measure (EuclideanSpace ℝ (Fin d)))
--       (B : Matrix (Fin n) (Fin n) ℝ)
--       (H E : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
--       (T J : EuclideanSpace ℝ (Fin d) → Fin m → Matrix (Fin n) (Fin n) ℝ)
--       (rho psi : EuclideanSpace ℝ (Fin d) → ℝ)
--       (dpsi : Fin m → EuclideanSpace ℝ (Fin d) → ℝ)
--       (hPair : ∀ l k i j : Fin n, Integrable (fun x => rho x *
--         (∑ a : Fin m, J x a i j * (psi x * T x a l k + dpsi a x * H x l k))) mu)
--       (hForce : ∀ l k i j : Fin n, Integrable
--         (fun x => rho x * E x i j * (psi x * H x l k)) mu)
--       (hTensor : ∀ a : Fin m, Integrable
--         (fun x => rho x * psi x * (2 * (B * T x a * B * J x a).trace)) mu)
--       (hFlux : ∀ a : Fin m, Integrable
--         (fun x => rho x * dpsi a x * (2 * (B * H x * B * J x a).trace)) mu)
--       (hTraceForce : Integrable
--         (fun x => rho x * psi x * (2 * (B * H x * B * E x).trace)) mu)
--       (hTest : ∀ l k i j : Fin n,
--         (∫ x, rho x * (∑ a : Fin m, J x a i j *
--           (psi x * T x a l k + dpsi a x * H x l k)) ∂mu) =
--         -(∫ x, rho x * E x i j * (psi x * H x l k) ∂mu)) :
--       (∫ x, rho x * (∑ a : Fin m, (2 * (B * H x * B * J x a).trace) * dpsi a x) ∂mu) =
--         -(∫ x, rho x *
--           (2 * (B * H x * B * E x).trace +
--             ∑ a : Fin m, 2 * (B * T x a * B * J x a).trace) * psi x ∂mu)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/WeakTrace`](https://prove2.me/theorems/4921a24d-b044-4852-b95d-96829251045f).
--
--   Supporting theorems: [`trace_mul_mul_mul_eq_sum`](https://prove2.me/theorems/341ba53c-b3cb-4ad0-873d-9d84885a6c75).
--
--   Next: [`integral_trace_quadratic_flux_eq_neg_density`](https://prove2.me/theorems/62d73344-315c-46bd-b8d0-841a9bad507d).
--
--   [Source excerpt, lines 48–72](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/WeakTrace.lean#L48-L72) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakTrace.lean#L48-L179 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakTrace`, declaration `_private.FunctionalInequalities.Analysis.Matrix.WeakTrace.0.FunctionalInequalities.Analysis.integral_trace_contraction_of_coordinate_pairings`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakTrace

open MeasureTheory Matrix

theorem FunctionalInequalities.Analysis.integral_trace_contraction_of_coordinate_pairings_readable {d n m : ℕ}
    (mu : Measure (EuclideanSpace ℝ (Fin d)))
    (B : Matrix (Fin n) (Fin n) ℝ)
    (H E : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    (T J : EuclideanSpace ℝ (Fin d) → Fin m → Matrix (Fin n) (Fin n) ℝ)
    (rho psi : EuclideanSpace ℝ (Fin d) → ℝ)
    (dpsi : Fin m → EuclideanSpace ℝ (Fin d) → ℝ)
    (hPair : ∀ l k i j : Fin n, Integrable (fun x => rho x *
      (∑ a : Fin m, J x a i j * (psi x * T x a l k + dpsi a x * H x l k))) mu)
    (hForce : ∀ l k i j : Fin n, Integrable
      (fun x => rho x * E x i j * (psi x * H x l k)) mu)
    (hTensor : ∀ a : Fin m, Integrable
      (fun x => rho x * psi x * (2 * (B * T x a * B * J x a).trace)) mu)
    (hFlux : ∀ a : Fin m, Integrable
      (fun x => rho x * dpsi a x * (2 * (B * H x * B * J x a).trace)) mu)
    (hTraceForce : Integrable
      (fun x => rho x * psi x * (2 * (B * H x * B * E x).trace)) mu)
    (hTest : ∀ l k i j : Fin n,
      (∫ x, rho x * (∑ a : Fin m, J x a i j *
        (psi x * T x a l k + dpsi a x * H x l k)) ∂mu) =
      -(∫ x, rho x * E x i j * (psi x * H x l k) ∂mu)) :
    (∫ x, rho x * (∑ a : Fin m, (2 * (B * H x * B * J x a).trace) * dpsi a x) ∂mu) =
      -(∫ x, rho x *
        (2 * (B * H x * B * E x).trace +
          ∑ a : Fin m, 2 * (B * T x a * B * J x a).trace) * psi x ∂mu) := by sorry
