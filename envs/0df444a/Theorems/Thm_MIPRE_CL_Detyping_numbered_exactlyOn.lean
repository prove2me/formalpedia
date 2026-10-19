-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_numbered_exactlyOn
-- name    : MIPRE.CL.Detyping.numbered_exactlyOn
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:22.771696+00:00
-- url     : https://prove2.me/theorems/4ae5cb21-5d0f-44c5-b03f-b6d7d629461b
-- title:
--   Lemma numbered_exactlyOn of the MIP* = RE formalization
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
--   theorem MIPRE.CL.Detyping.numbered_exactlyOn {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
--       (P : T → CLFun 𝔽₂ (Fin s) ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ) :
--       (numbered E w P).ExactlyOn univ
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.numbered_exactlyOn` is declared in `MIPRE/Foundations/CL/DetypingProgBits.lean`, lines 116–120. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgBits.lean#L116-L120

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

theorem MIPRE.CL.Detyping.numbered_exactlyOn {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ) :
    (numbered E w P).ExactlyOn univ := by sorry
