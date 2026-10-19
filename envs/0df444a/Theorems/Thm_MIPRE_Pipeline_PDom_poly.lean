-- Prove2me | Theorems.Thm_MIPRE_Pipeline_PDom_poly
-- name    : MIPRE.Pipeline.PDom.poly
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:25:56.544282+00:00
-- url     : https://prove2.me/theorems/74956fe4-b7b1-427f-be71-a2d0151e3426
-- title:
--   A fixed polynomial of a dominated quantity
-- statement:
--   A statement of the module `MIPRE.Foundations.Pipeline.PowDom` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Domination by a power of a monomial. The time bounds of the answer-reduced verifier (`thm:answer-reduction`) have the shape `(c (W + 1)^m X^e)^{K + 1}`: `W` a number dominating the parameters at index `n`, `X = |d| + 1` the size of the input and `K = μ` the input sampler's degree. It is the shape of the contract's `outBound bound λ μ σ n = P(L + σ)^{μ + 1}` at degree `d (μ + 1)`: one call to a sampler of coefficient `B ≤ W` and degree `K` on a query of size below `c (W + 1)^m X^e` costs `B (c (W + 1)^m X^e)^K`, which is of this shape (`ofCall`), and so is any fixed polynomial of such a cost…
--
--   **A fixed polynomial of a dominated quantity.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Pipeline
--   open MIPRE.Cost
--   variable {W X K : ℕ}
--
--   theorem MIPRE.Pipeline.PDom.poly (hX : 1 ≤ X) (P : Polynomial ℕ) {c m e y : ℕ} (h : PDom W X K c m e y) :
--       PDom W X K ((∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i + 1) * (c + 2) ^ P.natDegree)
--         (m * P.natDegree) (e * P.natDegree) (P.eval y)
--   ```
--
--   **Formalization Note** `MIPRE.Pipeline.PDom.poly` is declared in `MIPRE/Foundations/Pipeline/PowDom.lean`, lines 130–144. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/PowDom.lean#L130-L144

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom

open MIPRE
open MIPRE.Pipeline
open MIPRE.Cost
variable {W X K : ℕ}

theorem MIPRE.Pipeline.PDom.poly (hX : 1 ≤ X) (P : Polynomial ℕ) {c m e y : ℕ} (h : PDom W X K c m e y) :
    PDom W X K ((∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i + 1) * (c + 2) ^ P.natDegree)
      (m * P.natDegree) (e * P.natDegree) (P.eval y) := by sorry
