-- Prove2me | Theorems.Thm_MIPRE_AnswerReduction_Pcp_pt6_block
-- name    : MIPRE.AnswerReduction.Pcp.pt6_block
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:58:26.90402+00:00
-- url     : https://prove2.me/theorems/97e44cc6-4e25-497a-b813-fb10b883f61b
-- title:
--   The j-th coordinate of the i-th block of V_{6,pt} is the j-th coordinate of V_{i,pt}
-- statement:
--   A statement of the module `MIPRE.Background.AnswerReduction.PcpPresentation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The PCP sampler of answer reduction, over `F_q`. Piece AR-3a of `planning/answer-reduction.md`: the typed PCP sampler `Ŝ^pcp` of the paper's `sec:ar-verifier` (`ld_compiler.tex`, `eq:V-pcp`), as CL presentations over `F_q`. The ambient space is `V^pcp = ⊕_{i≤5} (V_{i,pt} ⊕ V_{i,coord} ⊕ V_{i,dir}) ⊕ V_{aux,pt} ⊕ V_{6,coord} ⊕ V_{aux,dir}`, with coordinates `Coord P` (`10m + 2s + 16` of them, `card_coord`). There are six copies of the seeded low-degree test on it (`regs`, `regs6`): * copy `i ≤ 5` is the test in `m` variables on its own three registers; * copy `6` is the test in `m' = 5m + 5 +…
--
--   The `j`-th coordinate of the `i`-th block of `V_{6,pt}` is the `j`-th coordinate of
--   `V_{i,pt}`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.AnswerReduction
--   open MIPRE.AnswerReduction.Pcp
--   open Finset MIPRE.LIDT MIPRE.LIDT.CL MIPRE.SAT
--   variable (P : PcpParams)
--
--   theorem MIPRE.AnswerReduction.Pcp.pt6_block (i : Fin 5) (j : Fin P.m) :
--       pt6 P ⟨i * P.m + j, by
--         have h1 : (i : ℕ) * P.m ≤ 4 * P.m := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp i.isLt)
--         have h2 : (j : ℕ) < P.m := j.isLt
--         simp only [PcpParams.m']
--         omega⟩ = .pt i j
--   ```
--
--   **Formalization Note** `MIPRE.AnswerReduction.Pcp.pt6_block` is declared in `MIPRE/Background/AnswerReduction/PcpPresentation.lean`, lines 148–169. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/PcpPresentation.lean#L148-L169

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation

open MIPRE
open MIPRE.AnswerReduction
open MIPRE.AnswerReduction.Pcp
open Finset MIPRE.LIDT MIPRE.LIDT.CL MIPRE.SAT
variable (P : PcpParams)

theorem MIPRE.AnswerReduction.Pcp.pt6_block (i : Fin 5) (j : Fin P.m) :
    pt6 P ⟨i * P.m + j, by
      have h1 : (i : ℕ) * P.m ≤ 4 * P.m := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp i.isLt)
      have h2 : (j : ℕ) < P.m := j.isLt
      simp only [PcpParams.m']
      omega⟩ = .pt i j := by sorry
