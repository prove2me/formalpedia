-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_numbered_linear_graph
-- name    : MIPRE.CL.Detyping.numbered_linear_graph
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:31.453792+00:00
-- url     : https://prove2.me/theorems/b4565e8b-7071-45c2-9e1e-b25aff0d7f0b
-- title:
--   Graph-level linear queries append a zero content block
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingProgQueries` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bit-list query formulas for the numbered detyping sampler. These identities connect the semantic CL construction to the executable router's graph-prefix and content-suffix operations. Prefix validity for forwarded content queries is derived from the original numbered prefix.
--
--   Graph-level linear queries append a zero content block.
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
--   theorem MIPRE.CL.Detyping.numbered_linear_graph {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
--       (P : T → CLFun 𝔽₂ (Fin s) ℓ) (k : ℕ) (hk : k < 2)
--       (u y : Cost.BitStr) (hu : u.length = graphDim T + s) (hy : y.length = graphDim T + s) :
--       toBits ((numbered E w P).mapOfPrefix k (ofBits (graphDim T + s) u) (ofBits (graphDim T + s) y)) =
--         graphBits ((Graph.presentation E w.toBool).mapOfPrefix k
--           (graphOfBits (u.take (graphDim T))) (graphOfBits (y.take (graphDim T)))) ++
--           List.replicate s false
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.numbered_linear_graph` is declared in `MIPRE/Foundations/CL/DetypingProgQueries.lean`, lines 79–95. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgQueries.lean#L79-L95

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

theorem MIPRE.CL.Detyping.numbered_linear_graph {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (k : ℕ) (hk : k < 2)
    (u y : Cost.BitStr) (hu : u.length = graphDim T + s) (hy : y.length = graphDim T + s) :
    toBits ((numbered E w P).mapOfPrefix k (ofBits (graphDim T + s) u) (ofBits (graphDim T + s) y)) =
      graphBits ((Graph.presentation E w.toBool).mapOfPrefix k
        (graphOfBits (u.take (graphDim T))) (graphOfBits (y.take (graphDim T)))) ++
        List.replicate s false := by sorry
