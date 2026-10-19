-- Prove2me | Theorems.Thm_MIPRE_POVM_ext_prime
-- name    : MIPRE.POVM.ext_prime
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:21:34.874977+00:00
-- url     : https://prove2.me/theorems/aaef5b67-653c-4e5f-91a2-e40b072db008
-- title:
--   A POVM is determined by its operators. The remaining fields are propositions
-- statement:
--   A statement of the module `MIPRE.Foundations.Distances` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Distance measures. This file contains the definitions of the blueprint subsection "Distance measures" (Section 2, "Foundations"): the dimension-normalized Hilbert--Schmidt inner product and squared norm on complex matrices, and the distance between two families of POVMs relative to a question distribution.
--
--   **A POVM is determined by its operators.** The remaining fields are propositions.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.POVM
--   open ComplexOrder Matrix
--   variable {n : Type*} [Fintype n]
--   variable {X A d : Type*} [Fintype X] [Fintype A] [Fintype d] [DecidableEq d]
--
--   theorem MIPRE.POVM.ext_prime {M N : POVM A d} (h : ∀ a, (((M.mats a)).val) = (((N.mats a)).val)) : M = N
--   ```
--
--   **Formalization Note** `MIPRE.POVM.ext_prime` is declared in `MIPRE/Foundations/Distances.lean`, lines 106–113. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository (there named `MIPRE.POVM.ext'`; renamed for the platform, which requires ASCII identifiers). The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Distances.lean#L106-L113; blueprint def:expanded-state

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances

open MIPRE
open MIPRE.POVM
open ComplexOrder Matrix
variable {n : Type*} [Fintype n]
variable {X A d : Type*} [Fintype X] [Fintype A] [Fintype d] [DecidableEq d]

theorem MIPRE.POVM.ext_prime {M N : POVM A d} (h : ∀ a, (((M.mats a)).val) = (((N.mats a)).val)) : M = N := by sorry
