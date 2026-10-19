-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryFiniteField_minpoly_natDegree_of_not_mem_range
-- name    : MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_of_not_mem_range
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:38.90001+00:00
-- url     : https://prove2.me/theorems/cda99ecd-8107-4a1e-9495-dd732ba4dbee
-- title:
--   In a binary extension of degree 2^(t+1), every element outside the index-two subfield has the full extension degree
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryFiniteFieldDegree` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Finite-field membership and exact degree in power-of-two extensions
--
--   In a binary extension of degree `2^(t+1)`, every element outside the
--   index-two subfield has the full extension degree.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open Polynomial
--
--   theorem MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_of_not_mem_range {K L : Type*} [Field K] [Field L]
--       [Finite K] [Algebra K L] [Algebra (ZMod 2) L] [FiniteDimensional (ZMod 2) L]
--       (t : ℕ) (hK : Nat.card K = 2 ^ (2 ^ t))
--       (hL : Module.finrank (ZMod 2) L = 2 ^ (t + 1)) (x : L)
--       (hx : x ∉ (algebraMap K L).range) :
--       (minpoly (ZMod 2) x).natDegree = 2 ^ (t + 1)
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_of_not_mem_range` is declared in `MIPRE/Foundations/LowDegree/BinaryFiniteFieldDegree.lean`, lines 31–54. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryFiniteFieldDegree.lean#L31-L54

import Mathlib.FieldTheory.Finite.Extension

open Polynomial

theorem MIPRE.LowDegree.BinaryFiniteField.minpoly_natDegree_of_not_mem_range {K L : Type*} [Field K] [Field L]
    [Finite K] [Algebra K L] [Algebra (ZMod 2) L] [FiniteDimensional (ZMod 2) L]
    (t : ℕ) (hK : Nat.card K = 2 ^ (2 ^ t))
    (hL : Module.finrank (ZMod 2) L = 2 ^ (t + 1)) (x : L)
    (hx : x ∉ (algebraMap K L).range) :
    (minpoly (ZMod 2) x).natDegree = 2 ^ (t + 1) := by sorry
