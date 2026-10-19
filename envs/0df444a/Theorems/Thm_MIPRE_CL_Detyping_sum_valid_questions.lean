-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_sum_valid_questions
-- name    : MIPRE.CL.Detyping.sum_valid_questions
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:19:59.122219+00:00
-- url     : https://prove2.me/theorems/086bfdd9-1c33-4e1c-9cea-c6a2f5149d53
-- title:
--   The joint valid-seed sum is exactly the typed edge-and-common-seed sum
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingLaw` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The joint law of detyped questions. On an ordered edge the graph view depends only on the player's own type. Conditioning on the valid-edge event gives the uniform ordered-edge law and one shared uniform content seed, exactly as in `types.tex`, `def:detyped-CL`.
--
--   The joint valid-seed sum is exactly the typed edge-and-common-seed sum.
--   In particular, no independence of the two content outputs is asserted or needed.
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
--   theorem MIPRE.CL.Detyping.sum_valid_questions {ℓ : ℕ} {M : Type*} [AddCommMonoid M]
--       (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
--       (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
--       (f : (Coord T ι → ZMod 2) → (Coord T ι → ZMod 2) → M) :
--       ∑ g ∈ Graph.validSeeds E, ∑ v : ι → ZMod 2,
--         f ((presentation E false (P false)).eval (Sum.elim g v))
--           ((presentation E true (P true)).eval (Sum.elim g v)) =
--       ∑ uv ∈ Graph.edges E, ∑ v : ι → ZMod 2,
--         f (Sum.elim (view E false uv.1) ((P false uv.1).eval v))
--           (Sum.elim (view E true uv.2) ((P true uv.2).eval v))
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.sum_valid_questions` is declared in `MIPRE/Foundations/CL/DetypingLaw.lean`, lines 80–102. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingLaw.lean#L80-L102; blueprint lem:detype-cl

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

theorem MIPRE.CL.Detyping.sum_valid_questions {ℓ : ℕ} {M : Type*} [AddCommMonoid M]
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (f : (Coord T ι → ZMod 2) → (Coord T ι → ZMod 2) → M) :
    ∑ g ∈ Graph.validSeeds E, ∑ v : ι → ZMod 2,
      f ((presentation E false (P false)).eval (Sum.elim g v))
        ((presentation E true (P true)).eval (Sum.elim g v)) =
    ∑ uv ∈ Graph.edges E, ∑ v : ι → ZMod 2,
      f (Sum.elim (view E false uv.1) ((P false uv.1).eval v))
        (Sum.elim (view E true uv.2) ((P true uv.2).eval v)) := by sorry
