-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_normalize_monic
-- name    : MIPRE.LowDegree.BinaryPolynomial.normalize_monic
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:23:34.842331+00:00
-- url     : https://prove2.me/theorems/0ae7f0e6-15a2-45d4-b0d3-5ca388d29420
-- title:
--   Remove trailing zero coefficients and separate the leading monic coefficient
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryRepresentation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Binary coefficient representations. The coefficient interpretation used by the public Shoup contract and by the independent polynomial algorithms. This module does not assume that an irreducible polynomial has already been constructed.
--
--   Remove trailing zero coefficients and separate the leading monic coefficient.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.Cost
--
--   theorem MIPRE.LowDegree.BinaryPolynomial.normalize_monic (l : BitStr) (h : (polyOfBits l).Monic) :
--       polyOfBits (l.take (polyOfBits l).natDegree ++ [true]) = polyOfBits l
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryPolynomial.normalize_monic` is declared in `MIPRE/Foundations/LowDegree/BinaryRepresentation.lean`, lines 52–76. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryRepresentation.lean#L52-L76; blueprint lem:effective-binary-field-arithmetic

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation

open MIPRE
open MIPRE.LowDegree
open MIPRE.Cost

theorem MIPRE.LowDegree.BinaryPolynomial.normalize_monic (l : BitStr) (h : (polyOfBits l).Monic) :
    polyOfBits (l.take (polyOfBits l).natDegree ++ [true]) = polyOfBits l := by sorry
