-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_complete_commutes_sample
-- name    : MIPRE.CL.Detyping.complete_commutes_sample
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:15.971633+00:00
-- url     : https://prove2.me/theorems/3ec2e44a-e518-44c4-942b-473d3c6145f0
-- title:
--   At each detyped seed, the two measurements commute if the original strategy is PCC
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingComplete` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). PCC completeness of finite-game detyping. The complete strategy uses the input strategy's dimension and one common measurement rule for both players. Invalid local graph views select a constant measurement. On jointly valid views, the original strategy is played on the same ordered edge and common content seed.
--
--   At each detyped seed, the two measurements commute if the original strategy is PCC.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.Detyping
--   open Finset Classical Matrix Kronecker
--   variable {T ι A : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
--
--   theorem MIPRE.CL.Detyping.complete_commutes_sample {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
--       (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
--       (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
--       (D : Question T ι → Question T ι → A → A → Bool)
--       (S : SyncStrategy (typedGame E hne P D).doubled) (hS : S.IsPCC) (a₀ : A)
--       (g : Graph.Coord T → ZMod 2) (z : ι → ZMod 2) (a b : A) :
--       let R := complete E hne P D S a₀
--       let x := (presentation E false (P false)).eval (Sum.elim g z)
--       let y := (presentation E true (P true)).eval (Sum.elim g z)
--       R.P.M (false, x) a * R.P.M (true, y) b = R.P.M (true, y) b * R.P.M (false, x) a
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.complete_commutes_sample` is declared in `MIPRE/Foundations/CL/DetypingComplete.lean`, lines 121–149. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingComplete.lean#L121-L149

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
import Definitions.Def_MIPRE_Foundations_CL_DetypingComplete

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open Finset Classical Matrix Kronecker
set_option linter.unusedSectionVars false
variable {T ι A : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A]

theorem MIPRE.CL.Detyping.complete_commutes_sample {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (hS : S.IsPCC) (a₀ : A)
    (g : Graph.Coord T → ZMod 2) (z : ι → ZMod 2) (a b : A) :
    let R := complete E hne P D S a₀
    let x := (presentation E false (P false)).eval (Sum.elim g z)
    let y := (presentation E true (P true)).eval (Sum.elim g z)
    R.P.M (false, x) a * R.P.M (true, y) b = R.P.M (true, y) b * R.P.M (false, x) a := by sorry
