-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_natDegree_polyOfBits_append_true
-- name    : MIPRE.LowDegree.BinaryPolynomial.natDegree_polyOfBits_append_true
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:15.903459+00:00
-- url     : https://prove2.me/theorems/f3191f53-c328-4e22-81c7-79be9d1f234f
-- title:
--   The degree of a supplied monic modulus is exactly its lower-coefficient width
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryCanonical` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Canonical binary polynomial degrees and monic division
--
--   The degree of a supplied monic modulus is exactly its lower-coefficient width.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryPolynomial
--   open MIPRE.Cost Polynomial
--
--   theorem MIPRE.LowDegree.BinaryPolynomial.natDegree_polyOfBits_append_true (p : BitStr) :
--       (polyOfBits (p ++ [true])).natDegree = p.length
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryPolynomial.natDegree_polyOfBits_append_true` is declared in `MIPRE/Foundations/LowDegree/BinaryCanonical.lean`, lines 33–37. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryCanonical.lean#L33-L37

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryPolynomial
open MIPRE.Cost Polynomial

theorem MIPRE.LowDegree.BinaryPolynomial.natDegree_polyOfBits_append_true (p : BitStr) :
    (polyOfBits (p ++ [true])).natDegree = p.length := by sorry
