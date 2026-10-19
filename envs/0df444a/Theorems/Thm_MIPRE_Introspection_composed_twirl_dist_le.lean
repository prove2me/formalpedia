-- Prove2me | Theorems.Thm_MIPRE_Introspection_composed_twirl_dist_le
-- name    : MIPRE.Introspection.composed_twirl_dist_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:09:27.219981+00:00
-- url     : https://prove2.me/theorems/a874c725-88da-484c-8c44-7ba848eed277
-- title:
--   Two reflective twirls stay close if each commutator is small and the second has an exact mirror
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ComposedTwirl` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Composed twirling from two commutator estimates
--
--   Two reflective twirls stay close if each commutator is small and the second has an exact mirror.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix
--   variable {dA dB I J A : Type*} [Fintype dA] [DecidableEq dA]
--
--   theorem MIPRE.Introspection.composed_twirl_dist_le (μ : I → ℝ) (ν : J → ℝ)
--       (hμ0 : ∀ i, 0 ≤ μ i) (hν0 : ∀ j, 0 ≤ ν j)
--       (hμ1 : ∑ i, μ i = 1) (hν1 : ∑ j, ν j = 1)
--       (ψ : dA × dB → ℂ) (M : POVM A dA)
--       (U : I → Matrix dA dA ℂ) (V : J → Matrix dA dA ℂ) (W : J → Matrix dB dB ℂ)
--       (hUsa : ∀ i, (U i)ᴴ = U i) (hUid : ∀ i, U i * U i = 1)
--       (hVsa : ∀ j, (V j)ᴴ = V j) (hVid : ∀ j, V j * V j = 1)
--       (hW : ∀ j, (W j)ᴴ * W j = 1) (hmirror : ∀ j, xSqNorm ψ (V j) (W j) = 0) :
--       (∑ a, stateSqNorm ψ
--         (unitaryTwirl ν V (unitaryTwirl μ U (M.mats a).val) - (M.mats a).val)) ≤
--         4 * (∑ i, μ i * ∑ a, stateSqNorm ψ ((M.mats a).val * U i - U i * (M.mats a).val)) +
--         4 * (∑ j, ν j * ∑ a, stateSqNorm ψ ((M.mats a).val * V j - V j * (M.mats a).val))
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.composed_twirl_dist_le` is declared in `MIPRE/Foundations/Introspection/ComposedTwirl.lean`, lines 37–72. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ComposedTwirl.lean#L37-L72; blueprint lem:pauli-two-sided-commutation

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance

open MIPRE
open MIPRE.Introspection
open Finset Matrix
variable {dA dB I J A : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I] [Fintype J] [Fintype A]

theorem MIPRE.Introspection.composed_twirl_dist_le (μ : I → ℝ) (ν : J → ℝ)
    (hμ0 : ∀ i, 0 ≤ μ i) (hν0 : ∀ j, 0 ≤ ν j)
    (hμ1 : ∑ i, μ i = 1) (hν1 : ∑ j, ν j = 1)
    (ψ : dA × dB → ℂ) (M : POVM A dA)
    (U : I → Matrix dA dA ℂ) (V : J → Matrix dA dA ℂ) (W : J → Matrix dB dB ℂ)
    (hUsa : ∀ i, (U i)ᴴ = U i) (hUid : ∀ i, U i * U i = 1)
    (hVsa : ∀ j, (V j)ᴴ = V j) (hVid : ∀ j, V j * V j = 1)
    (hW : ∀ j, (W j)ᴴ * W j = 1) (hmirror : ∀ j, xSqNorm ψ (V j) (W j) = 0) :
    (∑ a, stateSqNorm ψ
      (unitaryTwirl ν V (unitaryTwirl μ U (M.mats a).val) - (M.mats a).val)) ≤
      4 * (∑ i, μ i * ∑ a, stateSqNorm ψ ((M.mats a).val * U i - U i * (M.mats a).val)) +
      4 * (∑ j, ν j * ∑ a, stateSqNorm ψ ((M.mats a).val * V j - V j * (M.mats a).val)) := by sorry
