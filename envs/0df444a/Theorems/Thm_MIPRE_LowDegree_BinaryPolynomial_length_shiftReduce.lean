-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_shiftReduce
-- name    : MIPRE.LowDegree.BinaryPolynomial.length_shiftReduce
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:23:20.55598+00:00
-- url     : https://prove2.me/theorems/174556c0-af34-4e9e-9067-819c9e5f8c70
-- title:
--   Lemma length_shiftReduce of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryPolynomial` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Binary polynomial arithmetic on coefficient lists. Coefficient lists are little-endian. XOR implements addition, and multiplication by the indeterminate is reduced using the lower coefficients of a monic modulus. The semantic lemmas work in every characteristic-two commutative ring containing a root of that modulus; the programs are uniform in the coefficient lists.
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
--   theorem MIPRE.LowDegree.BinaryPolynomial.length_shiftReduce (p a : BitStr) (h : a.length = p.length) :
--       (shiftReduce p a).length = p.length
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryPolynomial.length_shiftReduce` is declared in `MIPRE/Foundations/LowDegree/BinaryPolynomial.lean`, lines 92–95. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryPolynomial.lean#L92-L95

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

theorem MIPRE.LowDegree.BinaryPolynomial.length_shiftReduce (p a : BitStr) (h : a.length = p.length) :
    (shiftReduce p a).length = p.length := by sorry
