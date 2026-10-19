-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_graphOfBits_take_eq
-- name    : MIPRE.CL.Detyping.graphOfBits_take_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:19.826437+00:00
-- url     : https://prove2.me/theorems/891e27c9-ed8e-4f7d-ae54-04e1b7d9bbe5
-- title:
--   Lemma graphOfBits_take_eq of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingProgBits` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Contiguous graph and content encodings for detyping. The abstract sum of graph and content registers is numbered with the graph first. Vector encodings are consequently ordinary concatenations of bit lists.
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
--   theorem MIPRE.CL.Detyping.graphOfBits_take_eq (l : Cost.BitStr) :
--       graphOfBits (T := T) (l.take (graphDim T)) = graphOfBits l
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.graphOfBits_take_eq` is declared in `MIPRE/Foundations/CL/DetypingProgBits.lean`, lines 49–51. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgBits.lean#L49-L51

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

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem MIPRE.CL.Detyping.graphOfBits_take_eq (l : Cost.BitStr) :
    graphOfBits (T := T) (l.take (graphDim T)) = graphOfBits l := by sorry
