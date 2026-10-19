-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_divModBits_width
-- name    : MIPRE.LowDegree.BinaryPolynomial.divModBits_width
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:38.521157+00:00
-- url     : https://prove2.me/theorems/cc9b165d-b43a-4374-8290-ccb45941bc8b
-- title:
--   Output widths are bounded by the input and divisor widths
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryDivision` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Division by binary monic polynomials. The divisor is represented by its lower coefficients `p`; the leading one is implicit. Horner long division keeps a fixed-width remainder and records each discarded leading coefficient in the quotient. Division by the constant one has a separate branch. No irreducibility or field structure is assumed.
--
--   Output widths are bounded by the input and divisor widths.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryPolynomial
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial
--   variable {R : Type*} [CommRing R] [CharP R 2]
--
--   theorem MIPRE.LowDegree.BinaryPolynomial.divModBits_width (p a : BitStr) :
--       (divModBits p a).1.length ≤ a.length ∧ (divModBits p a).2.length ≤ p.length
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryPolynomial.divModBits_width` is declared in `MIPRE/Foundations/LowDegree/BinaryDivision.lean`, lines 154–162. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryDivision.lean#L154-L162; blueprint lem:binary-monic-division

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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryPolynomial
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]

theorem MIPRE.LowDegree.BinaryPolynomial.divModBits_width (p a : BitStr) :
    (divModBits p a).1.length ≤ a.length ∧ (divModBits p a).2.length ≤ p.length := by sorry
