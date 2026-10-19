-- Prove2me | Theorems.Thm_MIPRE_SAT_BinField_eval_circuitBits_vecBits
-- name    : MIPRE.SAT.BinField.eval_circuitBits_vecBits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:37:45.24854+00:00
-- url     : https://prove2.me/theorems/27f18ed0-e8e0-43e1-b9f1-016111c5afcb
-- title:
--   The circuit evaluator on a raw vector computes the finite polynomial at the original typed point, for any correct coefficient representation
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.FieldVectors` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Encoded field vectors and their circuit-coordinate slices
--
--   The circuit evaluator on a raw vector computes the finite polynomial at
--   the original typed point, for any correct coefficient representation.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.BinField
--   open MIPRE.Cost MIPRE.LowDegree MIPRE.LowDegree.BinaryPolynomial
--   variable {k : ℕ} (E : BinField k)
--
--   theorem MIPRE.SAT.BinField.eval_circuitBits_vecBits (C : Circuit) (hC : C.WellFormed)
--       (p : BitStr) (hp : p ≠ []) (hpk : p.length = k)
--       [CharP E.carrier 2] (root : E.carrier)
--       (hroot : root ^ p.length = BinaryPolynomial.evalBits root p)
--       (hencode : ∀ a : E.carrier, BinaryPolynomial.evalBits root (E.toBits a) = a)
--       (v : Fin (C.inputs + C.size) → E.carrier) :
--       BinaryPolynomial.evalBits root (Circuit.circuitBits p
--         ((E.vecBits v).take C.inputs) ((E.vecBits v).drop C.inputs) C.gates) =
--         MvPolynomial.eval v C.finiteArith
--   ```
--
--   **Formalization Note** `MIPRE.SAT.BinField.eval_circuitBits_vecBits` is declared in `MIPRE/Foundations/SAT/FieldVectors.lean`, lines 51–86. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/FieldVectors.lean#L51-L86

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
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
import Definitions.Def_MIPRE_Foundations_SAT_FieldVectors

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.BinField
open MIPRE.Cost MIPRE.LowDegree MIPRE.LowDegree.BinaryPolynomial
variable {k : ℕ} (E : BinField k)

theorem MIPRE.SAT.BinField.eval_circuitBits_vecBits (C : Circuit) (hC : C.WellFormed)
    (p : BitStr) (hp : p ≠ []) (hpk : p.length = k)
    [CharP E.carrier 2] (root : E.carrier)
    (hroot : root ^ p.length = BinaryPolynomial.evalBits root p)
    (hencode : ∀ a : E.carrier, BinaryPolynomial.evalBits root (E.toBits a) = a)
    (v : Fin (C.inputs + C.size) → E.carrier) :
    BinaryPolynomial.evalBits root (Circuit.circuitBits p
      ((E.vecBits v).take C.inputs) ((E.vecBits v).drop C.inputs) C.gates) =
      MvPolynomial.eval v C.finiteArith := by sorry
