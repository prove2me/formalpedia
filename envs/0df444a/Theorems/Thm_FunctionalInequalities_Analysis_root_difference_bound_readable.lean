-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_root_difference_bound_readable
-- name    : FunctionalInequalities.Analysis.root_difference_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:52.018867+00:00
-- url     : https://prove2.me/theorems/45094b81-6a32-4174-a33a-b96d1b6184f4
-- title:
--   Matrix Square Root Difference Bound
-- statement:
--   This statement is a Sylvester-type estimate for two real matrices.
--
--   Let ι be a finite index type with decidable equality. Let S and T be matrices. Suppose S has quadratic floor a, T has quadratic floor b, and T is symmetric. Then
--
--   $$ (a+b)\,\|S-T\|_F\leq\|S^2-T^2\|_F.$$
--
--   Here $\|\cdot\|_F$ is the Frobenius norm represented by `matrixEntries`. The estimate does not require S and T to commute.
--
--   This bound is a reusable stability estimate for matrix square roots and inverse-square-root regularity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem root_difference_bound (S T : Matrix ι ι ℝ) {a b : ℝ}
--       (hS : QuadraticFloor S a) (hT : QuadraticFloor T b) (hSym : ∀ i j, T i j = T j i) :
--       (a + b) * ‖matrixEntries (S - T)‖ ≤ ‖matrixEntries (S * S - T * T)‖
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Positivity`](https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c).
--
--   Previous: [`exists_quadraticFloor_of_posDef`](https://prove2.me/theorems/151ec180-9404-48fb-af6c-ada52b2eac65) · Next: [`inverse_quadratic_young`](https://prove2.me/theorems/88b8a40a-52a8-4842-a7d8-a36165a50c94).
--
--   [Source excerpt, lines 247–249](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L247-L249) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L245-L268 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, declaration `FunctionalInequalities.Analysis.root_difference_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq ι]

theorem FunctionalInequalities.Analysis.root_difference_bound_readable (S T : Matrix ι ι ℝ) {a b : ℝ}
    (hS : QuadraticFloor S a) (hT : QuadraticFloor T b) (hSym : ∀ i j, T i j = T j i) :
    (a + b) * ‖matrixEntries (S - T)‖ ≤ ‖matrixEntries (S * S - T * T)‖ := by sorry
