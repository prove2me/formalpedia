-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_posSemidef_weightedGram_readable
-- name    : FunctionalInequalities.Analysis.posSemidef_weightedGram_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:59.431491+00:00
-- url     : https://prove2.me/theorems/b7c15040-db81-4850-95bc-cc1e4b6e1569
-- title:
--   Positive Semidefinite Weighted Gram Matrix
-- statement:
--   This statement establishes positivity of a weighted Gram matrix.
--
--   Let ι and κ be finite index types, let A be a real matrix on ι, and assume A is positive semidefinite. For an arbitrary family of real matrices Tᵢ indexed by κ, define G by
--
--   $$G_{ij}=\sum_{a,b,c,d}A_{ac}A_{bd}(T_i)_{ab}(T_j)_{cd}.$$
--
--   Then G is positive semidefinite. Equivalently, this is the matrix representation of F(A ⊗ A)Fᵀ, where F records the entries of the matrices Tᵢ.
--
--   This is a reusable finite-dimensional Gram-matrix construction for tensor and trace-energy estimates.
--
--   **Formalization Note** The matrix `Matrix.PosSemidef` and all sums range over finite types; no symmetry or definiteness beyond positive semidefiniteness of A is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem posSemidef_weightedGram (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
--       (T : κ → Matrix ι ι ℝ) :
--       (Matrix.of fun i j => ∑ a, ∑ b, ∑ c, ∑ d,
--         A a c * A b d * T i a b * T j c d).PosSemidef
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Positivity`](https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c).
--
--   Next: [`exists_quadraticFloor_of_posDef`](https://prove2.me/theorems/151ec180-9404-48fb-af6c-ada52b2eac65).
--
--   [Source excerpt, lines 47–50](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L47-L50) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L45-L70 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, declaration `FunctionalInequalities.Analysis.posSemidef_weightedGram`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem FunctionalInequalities.Analysis.posSemidef_weightedGram_readable (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (T : κ → Matrix ι ι ℝ) :
    (Matrix.of fun i j => ∑ a, ∑ b, ∑ c, ∑ d,
      A a c * A b d * T i a b * T j c d).PosSemidef := by sorry
