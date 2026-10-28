-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_inverseSqrt_mul_mul_inverseSqrt_readable
-- name    : FunctionalInequalities.Analysis.inverseSqrt_mul_mul_inverseSqrt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:56.015306+00:00
-- url     : https://prove2.me/theorems/88c3f67d-7fa1-4c20-b7d0-8fa8e80c182a
-- title:
--   Inverse Square Root Root Sandwich
-- statement:
--   This formalizes part of equation (67) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), concerning the inverse-square-root diffusion coefficient.
--
--   Let E be a finite-dimensional real inner-product space and let A:E→E be a positive continuous linear operator that is a unit. Let σ=`inverseSqrt A` be its principal inverse square root. Then
--
--   $$σAσ=\operatorname{id}_E.$$
--
--   Thus the inverse square root whitens A in the operator product, without any commutation assumption being added to the statement.
--
--   This identity is reusable in covariance normalization and localization arguments involving positive invertible operators.
--
--   **Formalization Note** The identity uses composition and multiplication of continuous linear maps; `IsPositive` and `IsUnit` are the exact Lean hypotheses.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inverseSqrt_mul_mul_inverseSqrt (A : E →L[ℝ] E) (hpos : A.IsPositive) (hunit : IsUnit A) :
--       inverseSqrt A * A * inverseSqrt A = 1
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533).
--
--   Next: [`locallyLipschitz_matrixEntries_sqrt`](https://prove2.me/theorems/5c4697cb-4b3d-46a3-98ab-b78c98b3d26d).
--
--   [Source excerpt, lines 130–131](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Operator/InverseSqrt.lean#L130-L131) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/InverseSqrt.lean#L127-L152 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.InverseSqrt`, declaration `FunctionalInequalities.Analysis.inverseSqrt_mul_mul_inverseSqrt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.inverseSqrt_mul_mul_inverseSqrt_readable (A : E →L[ℝ] E) (hpos : A.IsPositive) (hunit : IsUnit A) :
    inverseSqrt A * A * inverseSqrt A = 1 := by sorry
