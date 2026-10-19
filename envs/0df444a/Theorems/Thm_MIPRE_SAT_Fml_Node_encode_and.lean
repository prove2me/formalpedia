-- Prove2me | Theorems.Thm_MIPRE_SAT_Fml_Node_encode_and
-- name    : MIPRE.SAT.Fml.Node.encode_and
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:26:22.944884+00:00
-- url     : https://prove2.me/theorems/cd29e7fd-c00e-4d62-a77c-88ad733daec0
-- title:
--   Lemma encode_and of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Formula` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Boolean formulas and their circuits. A formula (`Fml`) is a tree of `and`, `or`, `not` over input bits and constants. Its post-order flattening (`Fml.flattenAt`) is a circuit in which every gate is read at most once (input bits are read through fresh `input` gates, which `Circuit.WellFormed` does not count), so a formula's circuit is well-formed whatever the formula (`Fml.toCircuit_wellFormed`), and computes the formula (`Fml.eval_toCircuit`). The describer of the succinct Cook–Levin theorem is built as a formula, which confines the circuit bookkeeping to this file…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Fml
--   open MIPRE.SAT.Fml.Node
--   open MIPRE.Cost
--
--   theorem MIPRE.SAT.Fml.Node.encode_and : (encode and : Data) = .cons (.ofNat 2) .nil
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Fml.Node.encode_and` is declared in `MIPRE/Foundations/SAT/Formula.lean`, lines 114–114. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Formula.lean#L114-L114

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Fml
open MIPRE.SAT.Fml.Node
open MIPRE.Cost

theorem MIPRE.SAT.Fml.Node.encode_and : (encode and : Data) = .cons (.ofNat 2) .nil := by sorry
