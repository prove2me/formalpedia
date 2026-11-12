-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_Arithmetic_rectangular_rpow_omega_le_of_rank_growth
-- name    : OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.rectangular_rpow_omega_le_of_rank_growth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:26.396664+00:00
-- url     : https://prove2.me/theorems/47096f87-9b53-40cd-aa72-5d07ebf2b53d
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.rectangular_rpow_omega_le_of_rank_growth: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.rectangular_rpow_omega_le_of_rank_growth` of [lean/OAI/LinearAlgebra/MatrixFields/Construction/InitialState.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Construction/InitialState.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic`, with `open scoped BigOperators Topology Polynomial`, `open MatrixMultiplication.Foundation`):
--
--   ```lean
--   theorem rectangular_rpow_omega_le_of_rank_growth
--       {a b : ℕ} {q C k : ℝ} (ha : 2 ≤ a) (hk : 0 ≤ k)
--       (hab : (a : ℝ) ^ k ≤ (b : ℝ))
--       (hout : (a : ℝ) ^ (2 : ℕ) ≤ q) (hin : (a * b : ℕ) ≤ q)
--       (R : ℕ → ℕ)
--       (hRank : ∀ t, MatrixMultiplication.Foundation.Tensor.RankAtMost
--         (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
--           (Fin (a ^ t)) (Fin (b ^ t)) (Fin (a ^ t))) (R t))
--       (hcost : ∀ t, (R t : ℝ) ≤ C * q ^ t) :
--       (a : ℝ) ^ rectangularOmega F k ≤ q
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.RankAtMost` and `OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.matrixCoefficients` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.rectangularOmega` (definitions bundle `OAIQ254M001` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.equalVolume_inequality_of_polynomialApproximation` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Construction/InitialState.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.rectangular_rpow_omega_le_of_rank_growth)

import Mathlib
import Definitions.Def_OAIQ254M000
import Definitions.Def_OAIQ254M001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace Arithmetic

variable {F : Type*} [Field F]

theorem rectangular_rpow_omega_le_of_rank_growth
    {a b : ℕ} {q C k : ℝ} (ha : 2 ≤ a) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ q) (hin : (a * b : ℕ) ≤ q)
    (R : ℕ → ℕ)
    (hRank : ∀ t, MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
        (Fin (a ^ t)) (Fin (b ^ t)) (Fin (a ^ t))) (R t))
    (hcost : ∀ t, (R t : ℝ) ≤ C * q ^ t) :
    (a : ℝ) ^ rectangularOmega F k ≤ q := by
  sorry

end Arithmetic
end MatrixMultiplication

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldFiniteFamily

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

end MatrixMultiplication.AllFieldFiniteFamily

end
end

end MatrixAllFields

end OAI
end
