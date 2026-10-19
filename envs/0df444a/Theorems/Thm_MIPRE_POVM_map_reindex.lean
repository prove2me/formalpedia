-- Prove2me | Theorems.Thm_MIPRE_POVM_map_reindex
-- name    : MIPRE.POVM.map_reindex
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:59.205241+00:00
-- url     : https://prove2.me/theorems/76b5eaff-bcb6-4d40-a7f8-4eff88ff48e0
-- title:
--   Reindexing the register commutes with relabelling the outcomes
-- statement:
--   A statement of the module `MIPRE.Foundations.RegisterReindex` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Reindexing the registers of a bipartite strategy. `TensorProductStrategy` (blueprint `def:tensor-strategy`) fixes the two players' registers to be `Fin dA` and `Fin dB`, and every soundness theorem proved through the vendored developments --- `MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL` in particular --- takes and returns its strategies in that form. The rigidity arguments of `MIPRE.QLD`, on the other hand, build their states and measurements on *structured* registers: a strategy's own space tensored with ancillas such as `(dA × Anc F m) × (F × F)`, where the block structure is what the…
--
--   Reindexing the register commutes with relabelling the outcomes.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.POVM
--   open Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {A : Type*} [Fintype A]
--   variable {d d' : Type*} [Fintype d] [Fintype d'] [DecidableEq d] [DecidableEq d']
--
--   theorem MIPRE.POVM.map_reindex {B : Type*} [Fintype B] [DecidableEq B] (e : d ≃ d') (f : A → B)
--       (M : POVM A d) : (M.map f).reindex e = (M.reindex e).map f
--   ```
--
--   **Formalization Note** `MIPRE.POVM.map_reindex` is declared in `MIPRE/Foundations/RegisterReindex.lean`, lines 105–111. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/RegisterReindex.lean#L105-L111

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B

open MIPRE
open MIPRE.POVM
open Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A]
variable {d d' : Type*} [Fintype d] [Fintype d'] [DecidableEq d] [DecidableEq d']

theorem MIPRE.POVM.map_reindex {B : Type*} [Fintype B] [DecidableEq B] (e : d ≃ d') (f : A → B)
    (M : POVM A d) : (M.map f).reindex e = (M.reindex e).map f := by sorry
