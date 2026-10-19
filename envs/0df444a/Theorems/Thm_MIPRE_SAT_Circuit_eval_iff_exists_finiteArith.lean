-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_eval_iff_exists_finiteArith
-- name    : MIPRE.SAT.Circuit.eval_iff_exists_finiteArith
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:59.492988+00:00
-- url     : https://prove2.me/theorems/51b9a445-c645-49af-b539-cba83e289fae
-- title:
--   Exact-variable arithmetization of the accepting circuit relation
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.FiniteCircuitArithmetization` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Circuit arithmetization on exactly the input and gate variables. The first `C.inputs` coordinates are the inputs, followed by the `C.size` gate variables. No new variables are needed for routing repeated input reads.
--
--   Exact-variable arithmetization of the accepting circuit relation.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Circuit
--   open MvPolynomial MIPRE.LowDegree
--   variable {F : Type*} [Field F]
--   variable [CharP F 2]
--
--   theorem MIPRE.SAT.Circuit.eval_iff_exists_finiteArith (C : Circuit) (hC : C.WellFormed) (x : ℕ → Bool) :
--       C.eval x = true ↔ ∃ z : Fin (C.inputs + C.size) → Bool,
--         (∀ i : Fin C.inputs, z (Fin.castAdd C.size i) = x i) ∧
--         MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 1
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.eval_iff_exists_finiteArith` is declared in `MIPRE/Foundations/SAT/FiniteCircuitArithmetization.lean`, lines 104–131. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/FiniteCircuitArithmetization.lean#L104-L131; blueprint lem:pcp-circuit-arithmetization

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
open MvPolynomial MIPRE.LowDegree
variable {F : Type*} [Field F]
variable [CharP F 2]

theorem MIPRE.SAT.Circuit.eval_iff_exists_finiteArith (C : Circuit) (hC : C.WellFormed) (x : ℕ → Bool) :
    C.eval x = true ↔ ∃ z : Fin (C.inputs + C.size) → Bool,
      (∀ i : Fin C.inputs, z (Fin.castAdd C.size i) = x i) ∧
      MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 1 := by sorry
