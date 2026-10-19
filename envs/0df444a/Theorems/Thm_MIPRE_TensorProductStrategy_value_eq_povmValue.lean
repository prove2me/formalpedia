-- Prove2me | Theorems.Thm_MIPRE_TensorProductStrategy_value_eq_povmValue
-- name    : MIPRE.TensorProductStrategy.value_eq_povmValue
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:09.436784+00:00
-- url     : https://prove2.me/theorems/7c4b4c98-dce9-4aa5-a845-850ee6c4af0e
-- title:
--   TensorProductStrategy.value is the povmValue of the strategy's own measurements, read as POVMs
-- statement:
--   A statement of the module `MIPRE.Foundations.RegisterReindex` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Reindexing the registers of a bipartite strategy. `TensorProductStrategy` (blueprint `def:tensor-strategy`) fixes the two players' registers to be `Fin dA` and `Fin dB`, and every soundness theorem proved through the vendored developments --- `MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL` in particular --- takes and returns its strategies in that form. The rigidity arguments of `MIPRE.QLD`, on the other hand, build their states and measurements on *structured* registers: a strategy's own space tensored with ancillas such as `(dA × Anc F m) × (F × F)`, where the block structure is what the…
--
--   **`TensorProductStrategy.value` is the `povmValue` of the strategy's own measurements**, read
--   as POVMs.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TensorProductStrategy
--   open Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--
--   theorem MIPRE.TensorProductStrategy.value_eq_povmValue {G : Game X Y A B}
--       (S : TensorProductStrategy G) :
--       S.value = povmValue G S.ψ (fun x => S.PA.toPOVM x) (fun y => S.PB.toPOVM y)
--   ```
--
--   **Formalization Note** `MIPRE.TensorProductStrategy.value_eq_povmValue` is declared in `MIPRE/Foundations/RegisterReindex.lean`, lines 217–224. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/RegisterReindex.lean#L217-L224

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
open MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem MIPRE.TensorProductStrategy.value_eq_povmValue {G : Game X Y A B}
    (S : TensorProductStrategy G) :
    S.value = povmValue G S.ψ (fun x => S.PA.toPOVM x) (fun y => S.PB.toPOVM y) := by sorry
