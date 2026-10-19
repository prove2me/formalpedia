-- Prove2me | Theorems.Thm_MIPRE_Introspection_TypedPresentation_factor_aux
-- name    : MIPRE.Introspection.TypedPresentation.factor_aux
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:40:47.3015+00:00
-- url     : https://prove2.me/theorems/93f81e1c-3c30-434c-abab-a5a3cbe2d0eb
-- title:
--   The first auxiliary factor consumes the register; later factors are empty
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.TypedPresentation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The typed introspection CL presentation. The three-level Pauli presentations are retained verbatim. Every auxiliary type uses the zero presentation, padded to three levels with a full factor partition. Both players use the same family. The corresponding finite game has an exactly uniform ordered-edge law, and the cross-introspection edge asks the two zero-content questions with probability the inverse edge count.
--
--   The first auxiliary factor consumes the register; later factors are empty.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.TypedPresentation
--   open Finset Classical
--   variable {PauliType F ι : Type*} [Fintype ι] [DecidableEq ι] [Semiring F] {ℓ : ℕ}
--
--   theorem MIPRE.Introspection.TypedPresentation.factor_aux (P : PauliType → CL.CLFun F ι 3) (t : AuxType ℓ)
--       (w : Bool) (j : ℕ) (u : ι → F) :
--       (family P (.inr (t, w))).factorOfPrefix j u = if j = 0 then univ else ∅
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.TypedPresentation.factor_aux` is declared in `MIPRE/Foundations/Introspection/TypedPresentation.lean`, lines 57–61. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TypedPresentation.lean#L57-L61; blueprint lem:intro-type-presentation

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.TypedPresentation
open Finset Classical
variable {PauliType F ι : Type*} [Fintype ι] [DecidableEq ι] [Semiring F] {ℓ : ℕ}

theorem MIPRE.Introspection.TypedPresentation.factor_aux (P : PauliType → CL.CLFun F ι 3) (t : AuxType ℓ)
    (w : Bool) (j : ℕ) (u : ι → F) :
    (family P (.inr (t, w))).factorOfPrefix j u = if j = 0 then univ else ∅ := by sorry
