-- Prove2me | Theorems.Thm_MIPRE_LIDT_Adapter_param_through_eq_of_mem
-- name    : MIPRE.LIDT.Adapter.param_through_eq_of_mem
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T23:13:15.290003+00:00
-- url     : https://prove2.me/theorems/1e5d3fed-61de-4194-9b35-3fa806af6e29
-- title:
--   And so does Line.param, on the canonical presentation the canonical-line test uses: the direction's first nonzero coordinate is 1 and the base point vanishes there, which is…
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Geometry` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 1: the two games describe the same lines. The seeded CL test `MIPRE.LIDT.CL.clGame` and the canonical-line test `MIPRE.LIDT.lidtGame` present a line differently, and the adapter of `planning/lidt-cl-adapter.md` has to know that the two presentations agree where they should. This file settles the axis-parallel case, which is the one that needs the canonical representative of `def:cl-canonical` to be *computed* rather than used abstractly. The seeded test's base point for direction `w` is `rep w u = canonLin (span {w}) u`, the canonical linear map with kernel `span…
--
--   And so does `Line.param`, on the canonical presentation the canonical-line test uses: the
--   direction's first nonzero coordinate is `1` and the base point vanishes there, which is what
--   makes reading off that one coordinate correct.
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
--   theorem MIPRE.LIDT.Adapter.param_through_eq_of_mem {v : Fin n → F} (hv : ∃ j, v j ≠ 0) (u : Fin n → F) (t : F) :
--       Line.param (Line.through u v) ((Line.through u v).1 + t • (Line.through u v).2) = t
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Adapter.param_through_eq_of_mem` is declared in `MIPRE/Background/LIDT/Adapter/Geometry.lean`, lines 337–369. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Geometry.lean#L337-L369

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

theorem MIPRE.LIDT.Adapter.param_through_eq_of_mem {v : Fin n → F} (hv : ∃ j, v j ≠ 0) (u : Fin n → F) (t : F) :
    Line.param (Line.through u v) ((Line.through u v).1 + t • (Line.through u v).2) = t := by sorry
