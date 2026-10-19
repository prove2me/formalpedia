-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_evalBits_factorBits
-- name    : MIPRE.SAT.Circuit.evalBits_factorBits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:37:33.619152+00:00
-- url     : https://prove2.me/theorems/5b5aea97-63e0-4ceb-a103-ce4499dbdb43
-- title:
--   Each computed factor evaluates to the corresponding polynomial factor
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.CircuitFieldCorrect` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Correctness of the executable circuit polynomial evaluator
--
--   Each computed factor evaluates to the corresponding polynomial factor.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Circuit
--   open MIPRE.Cost MIPRE.LowDegree MIPRE.LowDegree.BinaryPolynomial MvPolynomial Finset
--   variable {F : Type*} [Field F] [CharP F 2]
--
--   theorem MIPRE.SAT.Circuit.evalBits_factorBits (C : Circuit) (hC : C.WellFormed) (z : F) (p : BitStr)
--       (hp : p ≠ []) (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
--       (x w : List BitStr) (hxlen : C.inputs ≤ x.length) (hwlen : C.size ≤ w.length)
--       (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length)
--       (k : ℕ) (hk : k < C.size) :
--       BinaryPolynomial.evalBits z (factorBits (p, x, w, C.fieldHistory w k)
--         (C.gates.getD k (.const false), w.getD k [])) =
--         MvPolynomial.eval (Sum.elim (fun i => BinaryPolynomial.evalBits z (x.getD i []))
--           (fun j => BinaryPolynomial.evalBits z (w.getD j []))) (C.consistencyFactor k)
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.evalBits_factorBits` is declared in `MIPRE/Foundations/SAT/CircuitFieldCorrect.lean`, lines 84–115. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/CircuitFieldCorrect.lean#L84-L115

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_GateProg
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_InputRoutingProg
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_SAT_GateFieldEval
import Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldEval
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldCorrect

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
open MIPRE.Cost MIPRE.LowDegree MIPRE.LowDegree.BinaryPolynomial MvPolynomial Finset
variable {F : Type*} [Field F] [CharP F 2]

theorem MIPRE.SAT.Circuit.evalBits_factorBits (C : Circuit) (hC : C.WellFormed) (z : F) (p : BitStr)
    (hp : p ≠ []) (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (x w : List BitStr) (hxlen : C.inputs ≤ x.length) (hwlen : C.size ≤ w.length)
    (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length)
    (k : ℕ) (hk : k < C.size) :
    BinaryPolynomial.evalBits z (factorBits (p, x, w, C.fieldHistory w k)
      (C.gates.getD k (.const false), w.getD k [])) =
      MvPolynomial.eval (Sum.elim (fun i => BinaryPolynomial.evalBits z (x.getD i []))
        (fun j => BinaryPolynomial.evalBits z (w.getD j []))) (C.consistencyFactor k) := by sorry
