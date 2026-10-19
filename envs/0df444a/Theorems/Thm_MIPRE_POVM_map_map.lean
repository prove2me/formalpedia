-- Prove2me | Theorems.Thm_MIPRE_POVM_map_map
-- name    : MIPRE.POVM.map_map
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:21:37.432033+00:00
-- url     : https://prove2.me/theorems/91569839-35f0-4327-89cb-693c6d2534b2
-- title:
--   Relabelling twice is relabelling once: the level sets of g ∘ f are the unions of the level sets of f along the level sets of g
-- statement:
--   A statement of the module `MIPRE.Foundations.Distances` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Distance measures. This file contains the definitions of the blueprint subsection "Distance measures" (Section 2, "Foundations"): the dimension-normalized Hilbert--Schmidt inner product and squared norm on complex matrices, and the distance between two families of POVMs relative to a question distribution.
--
--   **Relabelling twice is relabelling once**: the level sets of `g ∘ f` are the unions of the
--   level sets of `f` along the level sets of `g`.
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
--   theorem MIPRE.POVM.map_map {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
--       (M : POVM A d) (f : A → B) (g : B → C) :
--       (M.map f).map g = M.map fun a => g (f a)
--   ```
--
--   **Formalization Note** `MIPRE.POVM.map_map` is declared in `MIPRE/Foundations/Distances.lean`, lines 120–140. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Distances.lean#L120-L140; blueprint def:expanded-state

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

theorem MIPRE.POVM.map_map {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (M : POVM A d) (f : A → B) (g : B → C) :
    (M.map f).map g = M.map fun a => g (f a) := by sorry
