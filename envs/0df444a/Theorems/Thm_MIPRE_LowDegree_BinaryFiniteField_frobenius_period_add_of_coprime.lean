-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryFiniteField_frobenius_period_add_of_coprime
-- name    : MIPRE.LowDegree.BinaryFiniteField.frobenius_period_add_of_coprime
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:23.350983+00:00
-- url     : https://prove2.me/theorems/f5f9146e-cf62-4310-bee3-8c50779626b3
-- title:
--   A period of a sum is a period of both summands when their given periods are coprime
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryCoprimeDegree` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Exact degrees of sums with coprime binary field degrees
--
--   A period of a sum is a period of both summands when their given periods are coprime.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryFiniteField
--   open Polynomial
--   variable {R : Type*} [CommRing R] [CharP R 2]
--
--   theorem MIPRE.LowDegree.BinaryFiniteField.frobenius_period_add_of_coprime (x y : R) (a b n : ℕ) (hab : a.Coprime b)
--       (hx : iterateFrobenius R 2 a x = x) (hy : iterateFrobenius R 2 b y = y)
--       (hs : iterateFrobenius R 2 n (x + y) = x + y) :
--       iterateFrobenius R 2 n x = x ∧ iterateFrobenius R 2 n y = y
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryFiniteField.frobenius_period_add_of_coprime` is declared in `MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean`, lines 38–92. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean#L38-L92

import Mathlib.FieldTheory.Finite.Extension
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryFiniteField
open Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]

theorem MIPRE.LowDegree.BinaryFiniteField.frobenius_period_add_of_coprime (x y : R) (a b n : ℕ) (hab : a.Coprime b)
    (hx : iterateFrobenius R 2 a x = x) (hy : iterateFrobenius R 2 b y = y)
    (hs : iterateFrobenius R 2 n (x + y) = x + y) :
    iterateFrobenius R 2 n x = x ∧ iterateFrobenius R 2 n y = y := by sorry
