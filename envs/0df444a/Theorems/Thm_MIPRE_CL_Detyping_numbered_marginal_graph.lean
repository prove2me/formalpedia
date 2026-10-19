-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_numbered_marginal_graph
-- name    : MIPRE.CL.Detyping.numbered_marginal_graph
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:30.214165+00:00
-- url     : https://prove2.me/theorems/6dc2e80f-f571-4f5b-8f1f-80fe24ad596e
-- title:
--   Through the first two levels only graph bits are nonzero
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingProgQueries` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bit-list query formulas for the numbered detyping sampler. These identities connect the semantic CL construction to the executable router's graph-prefix and content-suffix operations. Prefix validity for forwarded content queries is derived from the original numbered prefix.
--
--   Through the first two levels only graph bits are nonzero.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.Detyping
--   open Finset Classical
--   variable {T : Type*} [Fintype T] [DecidableEq T]
--
--   theorem MIPRE.CL.Detyping.numbered_marginal_graph {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
--       (P : T → CLFun 𝔽₂ (Fin s) ℓ) (j : ℕ) (hj : j ≤ 2)
--       (z : Cost.BitStr) (hz : z.length = graphDim T + s) :
--       toBits (((numbered E w P).truncate j).eval (ofBits (graphDim T + s) z)) =
--         graphBits (((Graph.presentation E w.toBool).truncate j).eval
--           (graphOfBits (z.take (graphDim T)))) ++ List.replicate s false
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.numbered_marginal_graph` is declared in `MIPRE/Foundations/CL/DetypingProgQueries.lean`, lines 56–64. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgQueries.lean#L56-L64

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem MIPRE.CL.Detyping.numbered_marginal_graph {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (j : ℕ) (hj : j ≤ 2)
    (z : Cost.BitStr) (hz : z.length = graphDim T + s) :
    toBits (((numbered E w P).truncate j).eval (ofBits (graphDim T + s) z)) =
      graphBits (((Graph.presentation E w.toBool).truncate j).eval
        (graphOfBits (z.take (graphDim T)))) ++ List.replicate s false := by sorry
