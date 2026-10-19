-- Prove2me | Theorems.Thm_MIPRE_SAT_Fml_refs_flattenAt
-- name    : MIPRE.SAT.Fml.refs_flattenAt
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:26:26.867988+00:00
-- url     : https://prove2.me/theorems/48814033-bc4b-4302-8842-4b93a7f5cdeb
-- title:
--   Every reference of the gate at position k of flattenAt base f lies in [base, base + k)
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Formula` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Boolean formulas and their circuits. A formula (`Fml`) is a tree of `and`, `or`, `not` over input bits and constants. Its post-order flattening (`Fml.flattenAt`) is a circuit in which every gate is read at most once (input bits are read through fresh `input` gates, which `Circuit.WellFormed` does not count), so a formula's circuit is well-formed whatever the formula (`Fml.toCircuit_wellFormed`), and computes the formula (`Fml.eval_toCircuit`). The describer of the succinct Cook–Levin theorem is built as a formula, which confines the circuit bookkeeping to this file…
--
--   Every reference of the gate at position `k` of `flattenAt base f` lies in `[base, base + k)`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Fml
--   open MIPRE.Cost
--
--   theorem MIPRE.SAT.Fml.refs_flattenAt (base : ℕ) : ∀ (f : Fml) (k : ℕ) (hk : k < (f.flattenAt base).length),
--       ∀ u ∈ (f.flattenAt base)[k].refs, base ≤ u ∧ u < base + k
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Fml.refs_flattenAt` is declared in `MIPRE/Foundations/SAT/Formula.lean`, lines 258–330. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Formula.lean#L258-L330

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
open MIPRE.Cost

theorem MIPRE.SAT.Fml.refs_flattenAt (base : ℕ) : ∀ (f : Fml) (k : ℕ) (hk : k < (f.flattenAt base).length),
    ∀ u ∈ (f.flattenAt base)[k].refs, base ≤ u ∧ u < base + k := by sorry
