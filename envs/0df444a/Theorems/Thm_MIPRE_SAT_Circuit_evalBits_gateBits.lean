-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_evalBits_gateBits
-- name    : MIPRE.SAT.Circuit.evalBits_gateBits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:12:56.340789+00:00
-- url     : https://prove2.me/theorems/4639d4a8-e1e0-4302-b9b3-38eba024acb6
-- title:
--   Correctness of all five gate operations over every characteristic-two ring containing a root of the supplied modulus
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.GateFieldEval` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Uniform field evaluation of a routed gate. Field elements are coefficient vectors modulo a supplied binary monic polynomial. Gate indices stay binary, including on malformed inputs.
--
--   Correctness of all five gate operations over every characteristic-two ring
--   containing a root of the supplied modulus.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Circuit
--   open MIPRE.Cost MIPRE.LowDegree MIPRE.LowDegree.BinaryPolynomial
--   variable {R : Type*} [CommRing R]
--
--   theorem MIPRE.SAT.Circuit.evalBits_gateBits [CharP R 2] (z : R) (p : BitStr) (hp : p ≠ [])
--       (hroot : z ^ p.length = BinaryPolynomial.evalBits z p) (x : ℕ → BitStr) (w : List BitStr) (g : Gate)
--       (hw : ∀ j ∈ g.refs, (w.getD j []).length = p.length) :
--       BinaryPolynomial.evalBits z (gateBits p x w g) =
--         gateValue (fun i => BinaryPolynomial.evalBits z (x i)) (fun j => BinaryPolynomial.evalBits z (w.getD j [])) g
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.evalBits_gateBits` is declared in `MIPRE/Foundations/SAT/GateFieldEval.lean`, lines 75–101. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/GateFieldEval.lean#L75-L101; blueprint lem:pcp-circuit-evaluator

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
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

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
open MIPRE.Cost MIPRE.LowDegree MIPRE.LowDegree.BinaryPolynomial
variable {R : Type*} [CommRing R]

theorem MIPRE.SAT.Circuit.evalBits_gateBits [CharP R 2] (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p) (x : ℕ → BitStr) (w : List BitStr) (g : Gate)
    (hw : ∀ j ∈ g.refs, (w.getD j []).length = p.length) :
    BinaryPolynomial.evalBits z (gateBits p x w g) =
      gateValue (fun i => BinaryPolynomial.evalBits z (x i)) (fun j => BinaryPolynomial.evalBits z (w.getD j [])) g := by sorry
