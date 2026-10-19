-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_post_apply
-- name    : MIPRE.CL.Detyping.DeciderProgram.post_apply
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:09:25.981081+00:00
-- url     : https://prove2.me/theorems/9f8d9a4d-f900-4c6e-b575-58d470043431
-- title:
--   Lemma post_apply of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingDeciderRoute` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The executable detyping decision router. This is an explicit ambient adaptation of `types.tex`'s detyped decider. Canonical field encodings and question dimensions are checked first. An outer answer cutoff is enforced globally, as required by the ambient verifier budget. Within that cutoff nonedge views accept, and edge views use the source typed answer cutoff before invoking the typed decider. No uniform graph compilation or absolute source-model timeout bound is claimed here. Thus malformed graph patterns in binary questions accept within the outer cutoff, while noncanonical raw data…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.Detyping
--   open MIPRE.CL.Detyping.DeciderProgram
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.CL.Detyping.Program
--   variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
--
--   theorem MIPRE.CL.Detyping.DeciderProgram.post_apply (ctx out : Data) : post (ctx, out) = encode (decide (out = encode true))
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.DeciderProgram.post_apply` is declared in `MIPRE/Foundations/CL/DetypingDeciderRoute.lean`, lines 169–169. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingDeciderRoute.lean#L169-L169

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
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
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open MIPRE.CL.Detyping.DeciderProgram
open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.CL.Detyping.Program
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]

theorem MIPRE.CL.Detyping.DeciderProgram.post_apply (ctx out : Data) : post (ctx, out) = encode (decide (out = encode true)) := by sorry
