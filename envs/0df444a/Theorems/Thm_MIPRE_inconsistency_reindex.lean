-- Prove2me | Theorems.Thm_MIPRE_inconsistency_reindex
-- name    : MIPRE.inconsistency_reindex
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:06.485159+00:00
-- url     : https://prove2.me/theorems/91bae2e6-bc1a-4cb6-b791-b20880a3ef11
-- title:
--   Inconsistency is invariant under reindexing the registers
-- statement:
--   A statement of the module `MIPRE.Foundations.RegisterReindex` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Reindexing the registers of a bipartite strategy. `TensorProductStrategy` (blueprint `def:tensor-strategy`) fixes the two players' registers to be `Fin dA` and `Fin dB`, and every soundness theorem proved through the vendored developments --- `MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL` in particular --- takes and returns its strategies in that form. The rigidity arguments of `MIPRE.QLD`, on the other hand, build their states and measurements on *structured* registers: a strategy's own space tensored with ancillas such as `(dA × Anc F m) × (F × F)`, where the block structure is what the…
--
--   **Inconsistency is invariant under reindexing the registers.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {dA dB dA' dB' : Type*}
--   variable [Fintype dA] [Fintype dB] [Fintype dA'] [Fintype dB']
--   variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dA'] [DecidableEq dB']
--   variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--
--   theorem MIPRE.inconsistency_reindex [DecidableEq A] (eA : dA ≃ dA') (eB : dB ≃ dB') (μ : X → ℝ)
--       (ψ : dA × dB → ℂ) (M : X → POVM A dA) (N : X → POVM A dB) :
--       inconsistency μ (reindexVec eA eB ψ) (fun x => (M x).reindex eA) (fun x => (N x).reindex eB)
--         = inconsistency μ ψ M N
--   ```
--
--   **Formalization Note** `MIPRE.inconsistency_reindex` is declared in `MIPRE/Foundations/RegisterReindex.lean`, lines 200–206. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/RegisterReindex.lean#L200-L206

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
open Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB dA' dB' : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dA'] [Fintype dB']
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dA'] [DecidableEq dB']
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem MIPRE.inconsistency_reindex [DecidableEq A] (eA : dA ≃ dA') (eB : dB ≃ dB') (μ : X → ℝ)
    (ψ : dA × dB → ℂ) (M : X → POVM A dA) (N : X → POVM A dB) :
    inconsistency μ (reindexVec eA eB ψ) (fun x => (M x).reindex eA) (fun x => (N x).reindex eB)
      = inconsistency μ ψ M N := by sorry
