-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_shiftReduce
-- name    : MIPRE.LowDegree.BinaryPolynomial.evalBits_shiftReduce
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:23:28.894477+00:00
-- url     : https://prove2.me/theorems/f893484b-820f-414e-956e-40947ea5b697
-- title:
--   Reduction is correct whenever the chosen element satisfies the monic modulus
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryPolynomial` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Binary polynomial arithmetic on coefficient lists. Coefficient lists are little-endian. XOR implements addition, and multiplication by the indeterminate is reduced using the lower coefficients of a monic modulus. The semantic lemmas work in every characteristic-two commutative ring containing a root of that modulus; the programs are uniform in the coefficient lists.
--
--   Reduction is correct whenever the chosen element satisfies the monic modulus.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryPolynomial
--   open MIPRE.Cost
--   variable {R : Type*} [CommRing R]
--
--   theorem MIPRE.LowDegree.BinaryPolynomial.evalBits_shiftReduce [CharP R 2] (z : R) (p a : BitStr)
--       (hlen : a.length = p.length) (hroot : z ^ p.length = evalBits z p) :
--       evalBits z (shiftReduce p a) = z * evalBits z a
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryPolynomial.evalBits_shiftReduce` is declared in `MIPRE/Foundations/LowDegree/BinaryPolynomial.lean`, lines 106–118. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryPolynomial.lean#L106-L118

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryPolynomial
open MIPRE.Cost
variable {R : Type*} [CommRing R]

theorem MIPRE.LowDegree.BinaryPolynomial.evalBits_shiftReduce [CharP R 2] (z : R) (p a : BitStr)
    (hlen : a.length = p.length) (hroot : z ^ p.length = evalBits z p) :
    evalBits z (shiftReduce p a) = z * evalBits z a := by sorry
