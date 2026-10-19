-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryFiniteField_minpoly_natDegree_add_of_coprime
-- name    : MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_add_of_coprime
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:21.02986+00:00
-- url     : https://prove2.me/theorems/f042a808-338f-42d1-ac60-b96898aaff8f
-- title:
--   Summing algebraic binary elements of coprime degrees multiplies their exact degrees
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryCoprimeDegree` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Exact degrees of sums with coprime binary field degrees
--
--   Summing algebraic binary elements of coprime degrees multiplies their exact degrees.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryFiniteField
--   open Polynomial
--   variable {R : Type*} [CommRing R] [CharP R 2]
--   variable {L : Type*} [Field L] [Algebra (ZMod 2) L]
--
--   theorem MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_add_of_coprime (x y : L)
--       (hx : IsIntegral (ZMod 2) x) (hy : IsIntegral (ZMod 2) y)
--       (hab : (minpoly (ZMod 2) x).natDegree.Coprime (minpoly (ZMod 2) y).natDegree) :
--       (minpoly (ZMod 2) (x + y)).natDegree =
--         (minpoly (ZMod 2) x).natDegree * (minpoly (ZMod 2) y).natDegree
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_add_of_coprime` is declared in `MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean`, lines 102–134. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean#L102-L134

import Mathlib.FieldTheory.Finite.Extension
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryFiniteField
open Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
variable {L : Type*} [Field L] [Algebra (ZMod 2) L]

theorem MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_add_of_coprime (x y : L)
    (hx : IsIntegral (ZMod 2) x) (hy : IsIntegral (ZMod 2) y)
    (hab : (minpoly (ZMod 2) x).natDegree.Coprime (minpoly (ZMod 2) y).natDegree) :
    (minpoly (ZMod 2) (x + y)).natDegree =
      (minpoly (ZMod 2) x).natDegree * (minpoly (ZMod 2) y).natDegree := by sorry
