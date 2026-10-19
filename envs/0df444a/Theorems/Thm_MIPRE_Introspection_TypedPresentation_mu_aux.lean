-- Prove2me | Theorems.Thm_MIPRE_Introspection_TypedPresentation_mu_aux
-- name    : MIPRE.Introspection.TypedPresentation.mu_aux
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:41:04.789391+00:00
-- url     : https://prove2.me/theorems/7e0e3aea-f042-44ae-8307-a3e8b55ddded
-- title:
--   A fixed edge between auxiliary types has exactly inverse-edge-count probability
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.TypedPresentation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The typed introspection CL presentation. The three-level Pauli presentations are retained verbatim. Every auxiliary type uses the zero presentation, padded to three levels with a full factor partition. Both players use the same family. The corresponding finite game has an exactly uniform ordered-edge law, and the cross-introspection edge asks the two zero-content questions with probability the inverse edge count.
--
--   A fixed edge between auxiliary types has exactly inverse-edge-count probability.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.TypedPresentation
--   open Finset Classical
--   variable {PauliType F ι : Type*} [Fintype ι] [DecidableEq ι] [Semiring F] {ℓ : ℕ}
--   variable [Fintype PauliType] [DecidableEq PauliType]
--
--   theorem MIPRE.Introspection.TypedPresentation.mu_aux (E : PauliType → PauliType → Bool) (X Z : PauliType)
--       (P : PauliType → CL.CLFun (ZMod 2) ι 3)
--       (D : CL.Detyping.Question (QuestionType PauliType ℓ) ι →
--         CL.Detyping.Question (QuestionType PauliType ℓ) ι → A → B → Bool)
--       (t u : AuxType ℓ) (w w' : Bool)
--       (h : TypeGraph.Adj E X Z (.inr (t, w)) (.inr (u, w'))) :
--       (game E X Z ℓ P D).μ (.inr (t, w), 0) (.inr (u, w'), 0) =
--         ((TypeGraph.edges E X Z ℓ).card : ℝ)⁻¹
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.TypedPresentation.mu_aux` is declared in `MIPRE/Foundations/Introspection/TypedPresentation.lean`, lines 81–112. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TypedPresentation.lean#L81-L112

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
variable [Fintype PauliType] [DecidableEq PauliType]
  {A B : Type*} [Fintype A] [Fintype B]

theorem MIPRE.Introspection.TypedPresentation.mu_aux (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) ι 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) ι →
      CL.Detyping.Question (QuestionType PauliType ℓ) ι → A → B → Bool)
    (t u : AuxType ℓ) (w w' : Bool)
    (h : TypeGraph.Adj E X Z (.inr (t, w)) (.inr (u, w'))) :
    (game E X Z ℓ P D).μ (.inr (t, w), 0) (.inr (u, w'), 0) =
      ((TypeGraph.edges E X Z ℓ).card : ℝ)⁻¹ := by sorry
