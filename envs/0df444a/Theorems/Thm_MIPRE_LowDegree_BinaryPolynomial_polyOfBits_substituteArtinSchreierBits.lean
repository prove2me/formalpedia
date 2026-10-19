-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_polyOfBits_substituteArtinSchreierBits
-- name    : MIPRE.LowDegree.BinaryPolynomial.polyOfBits_substituteArtinSchreierBits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:04.144348+00:00
-- url     : https://prove2.me/theorems/01989216-37fb-4de7-86f1-25f89a4df811
-- title:
--   The executable substitution agrees with polynomial composition
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryArtinSchreierProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Effective substitution by the Artin–Schreier polynomial
--
--   The executable substitution agrees with polynomial composition.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryPolynomial
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial
--
--   theorem MIPRE.LowDegree.BinaryPolynomial.polyOfBits_substituteArtinSchreierBits (a : BitStr) :
--       polyOfBits (substituteArtinSchreierBits a) = (polyOfBits a).comp (X ^ 2 + X)
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryPolynomial.polyOfBits_substituteArtinSchreierBits` is declared in `MIPRE/Foundations/LowDegree/BinaryArtinSchreierProg.lean`, lines 43–47. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryArtinSchreierProg.lean#L43-L47

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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryPolynomial
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial

theorem MIPRE.LowDegree.BinaryPolynomial.polyOfBits_substituteArtinSchreierBits (a : BitStr) :
    polyOfBits (substituteArtinSchreierBits a) = (polyOfBits a).comp (X ^ 2 + X) := by sorry
