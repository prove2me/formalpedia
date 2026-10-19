-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryFiniteField_mem_range_iff_pow_card
-- name    : MIPRE.LowDegree.BinaryFiniteField.mem_range_iff_pow_card
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:22.657438+00:00
-- url     : https://prove2.me/theorems/acc36ce5-2866-4b55-82dc-da4fb8c58a02
-- title:
--   The fixed points of the base field's cardinality power are exactly that field
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryFiniteFieldDegree` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Finite-field membership and exact degree in power-of-two extensions
--
--   The fixed points of the base field's cardinality power are exactly that field.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open Polynomial
--
--   theorem MIPRE.LowDegree.BinaryFiniteField.mem_range_iff_pow_card {K L : Type*} [Field K] [Field L] [Finite K]
--       [Algebra K L] (x : L) :
--       x ∈ (algebraMap K L).range ↔ x ^ Nat.card K = x
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryFiniteField.mem_range_iff_pow_card` is declared in `MIPRE/Foundations/LowDegree/BinaryFiniteFieldDegree.lean`, lines 15–29. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryFiniteFieldDegree.lean#L15-L29

import Mathlib.FieldTheory.Finite.Extension

open Polynomial

theorem MIPRE.LowDegree.BinaryFiniteField.mem_range_iff_pow_card {K L : Type*} [Field K] [Field L] [Finite K]
    [Algebra K L] (x : L) :
    x ∈ (algebraMap K L).range ↔ x ^ Nat.card K = x := by sorry
