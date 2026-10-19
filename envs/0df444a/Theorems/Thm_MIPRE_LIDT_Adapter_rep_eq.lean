-- Prove2me | Theorems.Thm_MIPRE_LIDT_Adapter_rep_eq
-- name    : MIPRE.LIDT.Adapter.rep_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T23:13:47.330179+00:00
-- url     : https://prove2.me/theorems/1348018f-9f4b-4d03-bdbf-6ab6bdcd70dd
-- title:
--   The seeded test's base point, in closed form
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Geometry` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 1: the two games describe the same lines. The seeded CL test `MIPRE.LIDT.CL.clGame` and the canonical-line test `MIPRE.LIDT.lidtGame` present a line differently, and the adapter of `planning/lidt-cl-adapter.md` has to know that the two presentations agree where they should. This file settles the axis-parallel case, which is the one that needs the canonical representative of `def:cl-canonical` to be *computed* rather than used abstractly. The seeded test's base point for direction `w` is `rep w u = canonLin (span {w}) u`, the canonical linear map with kernel `span…
--
--   **The seeded test's base point, in closed form.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.Adapter
--   open Finset Submodule Module MIPRE.CL
--   variable {F : Type*} [Field F] {n : ℕ}
--   variable [DecidableEq F]
--
--   theorem MIPRE.LIDT.Adapter.rep_eq {w : Fin n → F} (hw : ∃ j, w j ≠ 0) (x : Fin n → F) :
--       canonLin (span F {w}) x
--         = x - (x (Fin.find (fun j => w j ≠ 0) hw)
--             / w (Fin.find (fun j => w j ≠ 0) hw)) • w
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Adapter.rep_eq` is declared in `MIPRE/Background/LIDT/Adapter/Geometry.lean`, lines 419–435. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Geometry.lean#L419-L435

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]

theorem MIPRE.LIDT.Adapter.rep_eq {w : Fin n → F} (hw : ∃ j, w j ≠ 0) (x : Fin n → F) :
    canonLin (span F {w}) x
      = x - (x (Fin.find (fun j => w j ≠ 0) hw)
          / w (Fin.find (fun j => w j ≠ 0) hw)) • w := by sorry
