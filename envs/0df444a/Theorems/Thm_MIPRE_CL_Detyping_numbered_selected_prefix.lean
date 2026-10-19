-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_numbered_selected_prefix
-- name    : MIPRE.CL.Detyping.numbered_selected_prefix
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:35.402325+00:00
-- url     : https://prove2.me/theorems/a693fc02-b05a-4de3-91d5-a70c63011819
-- title:
--   A selected type receives a prefix that is valid for the original typed sampler
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingProgQueries` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bit-list query formulas for the numbered detyping sampler. These identities connect the semantic CL construction to the executable router's graph-prefix and content-suffix operations. Prefix validity for forwarded content queries is derived from the original numbered prefix.
--
--   A selected type receives a prefix that is valid for the original typed sampler.
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
--   theorem MIPRE.CL.Detyping.numbered_selected_prefix {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
--       (P : T → CLFun 𝔽₂ (Fin s) ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
--       (r : ℕ) (hr : 1 ≤ r) (u : Cost.BitStr)
--       (hu : ∃ x, u = toBits (((numbered E w P).truncate (r + 1)).eval x))
--       {t : T} (ht : select E w.toBool (graphOfBits (u.take (graphDim T))) = some t) :
--       ∃ v, u.drop (graphDim T) = toBits (((P t).truncate (r - 1)).eval v)
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.numbered_selected_prefix` is declared in `MIPRE/Foundations/CL/DetypingProgQueries.lean`, lines 182–197. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgQueries.lean#L182-L197

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

theorem MIPRE.CL.Detyping.numbered_selected_prefix {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (r : ℕ) (hr : 1 ≤ r) (u : Cost.BitStr)
    (hu : ∃ x, u = toBits (((numbered E w P).truncate (r + 1)).eval x))
    {t : T} (ht : select E w.toBool (graphOfBits (u.take (graphDim T))) = some t) :
    ∃ v, u.drop (graphDim T) = toBits (((P t).truncate (r - 1)).eval v) := by sorry
