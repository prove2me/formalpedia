-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_quadraticFloor_of_posDef_readable
-- name    : FunctionalInequalities.Analysis.exists_quadraticFloor_of_posDef_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:33.800484+00:00
-- url     : https://prove2.me/theorems/151ec180-9404-48fb-af6c-ada52b2eac65
-- title:
--   Positive Quadratic Floor for Positive-Definite Matrices
-- statement:
--   Let $\iota$ be a finite index type and let $S$ be a positive-definite real matrix indexed by $\iota$. Then there exists $a>0$ such that `QuadraticFloor S a` holds; equivalently, every vector $v$ satisfies
--
--   $$a\|v\|^2\le\langle v,Sv\rangle.$$
--
--   The conclusion also covers the empty index type, where the theorem supplies the explicit floor $a=1$. This is a finite-dimensional matrix positivity lemma.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_quadraticFloor_of_posDef {S : Matrix ι ι ℝ} (hS : S.PosDef) :
--       ∃ a : ℝ, 0 < a ∧ QuadraticFloor S a
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Positivity`](https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c).
--
--   Previous: [`posSemidef_weightedGram`](https://prove2.me/theorems/b7c15040-db81-4850-95bc-cc1e4b6e1569) · Next: [`root_difference_bound`](https://prove2.me/theorems/45094b81-6a32-4174-a33a-b96d1b6184f4).
--
--   [Source excerpt, lines 133–134](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L133-L134) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L131-L145 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, declaration `FunctionalInequalities.Analysis.exists_quadraticFloor_of_posDef`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq ι]

theorem FunctionalInequalities.Analysis.exists_quadraticFloor_of_posDef_readable {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    ∃ a : ℝ, 0 < a ∧ QuadraticFloor S a := by sorry
