-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
-- name    : MIPRE.LowDegree.BinaryPolynomial.evalBits_oneBits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:13.987757+00:00
-- url     : https://prove2.me/theorems/033788e8-b95f-484e-83d9-bb6316b69014
-- title:
--   Lemma evalBits_oneBits of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryConstants` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Fixed-width zero and one for binary polynomial quotients
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
--   theorem MIPRE.LowDegree.BinaryPolynomial.evalBits_oneBits (z : R) (p : BitStr) (hp : p ≠ []) : evalBits z (oneBits p) = 1
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryPolynomial.evalBits_oneBits` is declared in `MIPRE/Foundations/LowDegree/BinaryConstants.lean`, lines 31–32. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryConstants.lean#L31-L32

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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryPolynomial
open MIPRE.Cost
variable {R : Type*} [CommRing R]

theorem MIPRE.LowDegree.BinaryPolynomial.evalBits_oneBits (z : R) (p : BitStr) (hp : p ≠ []) : evalBits z (oneBits p) = 1 := by sorry
