-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_toBits_ofBits
-- name    : MIPRE.LowDegree.BinaryQuotient.toBits_ofBits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:24.211992+00:00
-- url     : https://prove2.me/theorems/65e7db70-4043-4a1a-9873-2bf72e685067
-- title:
--   Every correctly sized list is already the canonical quotient encoding
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryQuotient` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Coordinates for arbitrary monic binary polynomial quotients. The basis and coefficient representation require only monicity. In particular, the modulus need not be irreducible or squarefree. The abstract coordinate maps are used in proofs; the executable addition and multiplication are the existing uniform coefficient-list programs.
--
--   Every correctly sized list is already the canonical quotient encoding.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryQuotient
--   open MIPRE.Cost MIPRE.LowDegree.BinaryPolynomial
--   variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
--
--   theorem MIPRE.LowDegree.BinaryQuotient.toBits_ofBits (l : BitStr) (hlen : l.length = f.natDegree) :
--       toBits f hf (ofBits f hf l) = l
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryQuotient.toBits_ofBits` is declared in `MIPRE/Foundations/LowDegree/BinaryQuotient.lean`, lines 62–76. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryQuotient.lean#L62-L76; blueprint lem:binary-monic-quotient

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryQuotient
open MIPRE.Cost MIPRE.LowDegree.BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)

theorem MIPRE.LowDegree.BinaryQuotient.toBits_ofBits (l : BitStr) (hlen : l.length = f.natDegree) :
    toBits f hf (ofBits f hf l) = l := by sorry
