-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_gcdStep_correct
-- name    : MIPRE.LowDegree.BinaryPolynomial.gcdStep_correct
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:31.379986+00:00
-- url     : https://prove2.me/theorems/005e21bb-7db3-4b95-93b1-9f62868446c0
-- title:
--   Each division step preserves the polynomial gcd and the canonical-divisor invariant
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryGCD` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Deterministic binary polynomial gcd. Euclidean division decreases the canonical divisor width. The original divisor list supplies the iteration budget, and a zero-divisor state is absorbing. The same width bound holds for malformed states, so the ambient program has a global polynomial bound rather than a promise only on well-formed inputs.
--
--   Each division step preserves the polynomial gcd and the canonical-divisor invariant.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryPolynomial
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial
--
--   theorem MIPRE.LowDegree.BinaryPolynomial.gcdStep_correct (s : GCDState) (b : Bool)
--       (hs : s.2 = [] ∨ s.2.getLastD false = true) :
--       gcd (polyOfBits (gcdStep s b).1) (polyOfBits (gcdStep s b).2) =
--         gcd (polyOfBits s.1) (polyOfBits s.2) ∧
--       ((gcdStep s b).2 = [] ∨ (gcdStep s b).2.getLastD false = true)
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryPolynomial.gcdStep_correct` is declared in `MIPRE/Foundations/LowDegree/BinaryGCD.lean`, lines 73–94. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryGCD.lean#L73-L94

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Content
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryPolynomial
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial

theorem MIPRE.LowDegree.BinaryPolynomial.gcdStep_correct (s : GCDState) (b : Bool)
    (hs : s.2 = [] ∨ s.2.getLastD false = true) :
    gcd (polyOfBits (gcdStep s b).1) (polyOfBits (gcdStep s b).2) =
      gcd (polyOfBits s.1) (polyOfBits s.2) ∧
    ((gcdStep s b).2 = [] ∨ (gcdStep s b).2.getLastD false = true) := by sorry
