-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_decodeView_output
-- name    : MIPRE.CL.Detyping.decodeView_output
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:52.997959+00:00
-- url     : https://prove2.me/theorems/bd6eec2d-cbb7-4dfe-b494-c422805dd182
-- title:
--   On a sampled graph view, the common decoder is exactly the local selector
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingCompleteSupport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The common measurement rule and support of detyping. Both players use one decoder of graph views. It agrees with their own type selector on sampled questions, and otherwise selects a deterministic fallback. This is the player-independent rule in `types.tex`, `lem:detyping-verifiers`.
--
--   On a sampled graph view, the common decoder is exactly the local selector.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.Detyping
--   open Finset Classical
--   variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
--
--   theorem MIPRE.CL.Detyping.decodeView_output (E : T → T → Prop) [DecidableRel E] (w : Bool)
--       (g : Graph.Coord T → ZMod 2) :
--       decodeView E ((Graph.presentation E w).eval g) = (select E w g).map (w, ·)
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.decodeView_output` is declared in `MIPRE/Foundations/CL/DetypingCompleteSupport.lean`, lines 71–87. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingCompleteSupport.lean#L71-L87

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingCompleteSupport

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

theorem MIPRE.CL.Detyping.decodeView_output (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) :
    decodeView E ((Graph.presentation E w).eval g) = (select E w g).map (w, ·) := by sorry
