-- Prove2me | Theorems.Thm_MIPRE_LIDT_Adapter_through_eq_through_iff
-- name    : MIPRE.LIDT.Adapter.through_eq_through_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T23:13:59.782695+00:00
-- url     : https://prove2.me/theorems/32593e54-cd2a-4273-9408-ca85feaf6d4b
-- title:
--   Two lines through the same point coincide exactly when their directions are proportional
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Geometry` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 1: the two games describe the same lines. The seeded CL test `MIPRE.LIDT.CL.clGame` and the canonical-line test `MIPRE.LIDT.lidtGame` present a line differently, and the adapter of `planning/lidt-cl-adapter.md` has to know that the two presentations agree where they should. This file settles the axis-parallel case, which is the one that needs the canonical representative of `def:cl-canonical` to be *computed* rather than used abstractly. The seeded test's base point for direction `w` is `rep w u = canonLin (span {w}) u`, the canonical linear map with kernel `span…
--
--   **Two lines through the same point coincide exactly when their directions are
--   proportional.**
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
--   theorem MIPRE.LIDT.Adapter.through_eq_through_iff {u w z : Fin n → F} (hw : ∃ k, w k ≠ 0) (hz : ∃ k, z k ≠ 0) :
--       Line.through u z = Line.through u w ↔ ∃ c : F, c ≠ 0 ∧ z = c • w
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Adapter.through_eq_through_iff` is declared in `MIPRE/Background/LIDT/Adapter/Geometry.lean`, lines 477–508. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Geometry.lean#L477-L508

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

theorem MIPRE.LIDT.Adapter.through_eq_through_iff {u w z : Fin n → F} (hw : ∃ k, w k ≠ 0) (hz : ∃ k, z k ≠ 0) :
    Line.through u z = Line.through u w ↔ ∃ c : F, c ≠ 0 ∧ z = c • w := by sorry
