-- Prove2me | Theorems.Thm_MIPRE_Pipeline_PDom_ofCallPow
-- name    : MIPRE.Pipeline.PDom.ofCallPow
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:25:56.717799+00:00
-- url     : https://prove2.me/theorems/dbe7769e-ee94-4140-bd78-e784038b1378
-- title:
--   One call to a program of coefficient B ≤ c₀ (W + 1)^{m₀} and degree e' (K + 1), on a query of size below the unpowered monomial c₁ (W + 1)^{m₁} X^{e₁}
-- statement:
--   A statement of the module `MIPRE.Foundations.Pipeline.PowDom` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Domination by a power of a monomial. The time bounds of the answer-reduced verifier (`thm:answer-reduction`) have the shape `(c (W + 1)^m X^e)^{K + 1}`: `W` a number dominating the parameters at index `n`, `X = |d| + 1` the size of the input and `K = μ` the input sampler's degree. It is the shape of the contract's `outBound bound λ μ σ n = P(L + σ)^{μ + 1}` at degree `d (μ + 1)`: one call to a sampler of coefficient `B ≤ W` and degree `K` on a query of size below `c (W + 1)^m X^e` costs `B (c (W + 1)^m X^e)^K`, which is of this shape (`ofCall`), and so is any fixed polynomial of such a cost…
--
--   **One call to a program** of coefficient `B ≤ c₀ (W + 1)^{m₀}` and degree `e' (K + 1)`, on a
--   query of size below the unpowered monomial `c₁ (W + 1)^{m₁} X^{e₁}`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Pipeline
--   open MIPRE.Cost
--   variable {W X K : ℕ}
--
--   theorem MIPRE.Pipeline.PDom.ofCallPow {B q t c₀ m₀ c₁ m₁ e₁ e' : ℕ} (hB : B ≤ c₀ * (W + 1) ^ m₀)
--       (hq : q + 1 ≤ c₁ * (W + 1) ^ m₁ * X ^ e₁) (ht : t ≤ B * (q + 1) ^ (e' * (K + 1))) :
--       PDom W X K (c₀ * c₁ ^ e') (m₀ + m₁ * e') (e₁ * e') t
--   ```
--
--   **Formalization Note** `MIPRE.Pipeline.PDom.ofCallPow` is declared in `MIPRE/Foundations/Pipeline/PowDom.lean`, lines 160–177. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/PowDom.lean#L160-L177

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

theorem MIPRE.Pipeline.PDom.ofCallPow {B q t c₀ m₀ c₁ m₁ e₁ e' : ℕ} (hB : B ≤ c₀ * (W + 1) ^ m₀)
    (hq : q + 1 ≤ c₁ * (W + 1) ^ m₁ * X ^ e₁) (ht : t ≤ B * (q + 1) ^ (e' * (K + 1))) :
    PDom W X K (c₀ * c₁ ^ e') (m₀ + m₁ * e') (e₁ * e') t := by sorry
