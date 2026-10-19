-- Prove2me | Theorems.Thm_MIPRE_bornProb_reindex
-- name    : MIPRE.bornProb_reindex
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:57.993994+00:00
-- url     : https://prove2.me/theorems/bbf93c6b-1de6-4a3a-8c1c-4bf2ecb349f6
-- title:
--   Lemma bornProb_reindex of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.RegisterReindex` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Reindexing the registers of a bipartite strategy. `TensorProductStrategy` (blueprint `def:tensor-strategy`) fixes the two players' registers to be `Fin dA` and `Fin dB`, and every soundness theorem proved through the vendored developments --- `MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL` in particular --- takes and returns its strategies in that form. The rigidity arguments of `MIPRE.QLD`, on the other hand, build their states and measurements on *structured* registers: a strategy's own space tensored with ancillas such as `(dA × Anc F m) × (F × F)`, where the block structure is what the…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {dA dB dA' dB' : Type*}
--   variable [Fintype dA] [Fintype dB] [Fintype dA'] [Fintype dB']
--
--   theorem MIPRE.bornProb_reindex (eA : dA ≃ dA') (eB : dB ≃ dB') (ψ : dA × dB → ℂ)
--       (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) :
--       bornProb (reindexVec eA eB ψ) (Matrix.reindex eA eA EA) (Matrix.reindex eB eB EB)
--         = bornProb ψ EA EB
--   ```
--
--   **Formalization Note** `MIPRE.bornProb_reindex` is declared in `MIPRE/Foundations/RegisterReindex.lean`, lines 183–187. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/RegisterReindex.lean#L183-L187

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

theorem MIPRE.bornProb_reindex (eA : dA ≃ dA') (eB : dB ≃ dB') (ψ : dA × dB → ℂ)
    (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) :
    bornProb (reindexVec eA eB ψ) (Matrix.reindex eA eA EA) (Matrix.reindex eB eB EB)
      = bornProb ψ EA EB := by sorry
