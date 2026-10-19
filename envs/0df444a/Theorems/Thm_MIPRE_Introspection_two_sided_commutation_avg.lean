-- Prove2me | Theorems.Thm_MIPRE_Introspection_two_sided_commutation_avg
-- name    : MIPRE.Introspection.two_sided_commutation_avg
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:11:41.94309+00:00
-- url     : https://prove2.me/theorems/6ef4f150-becc-44b8-ad71-61479b3a20d7
-- title:
--   Independent conditional unitary distributions preserve the same explicit constants
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.TwoSidedCommutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Combining approximate commutations across a bipartite state. Transfer the second unitary to the other party, commute the first, and transfer back. The POVM square-sum bound controls both transfer errors without an alphabet factor.
--
--   Independent conditional unitary distributions preserve the same explicit constants.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--
--   theorem MIPRE.Introspection.two_sided_commutation_avg {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
--       (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
--       (μ : X → I → ℝ) (ν : X → J → ℝ)
--       (hμ0 : ∀ x i, 0 ≤ μ x i) (hν0 : ∀ x j, 0 ≤ ν x j)
--       (hμ1 : ∀ x, ∑ i, μ x i = 1) (hν1 : ∀ x, ∑ j, ν x j = 1)
--       (ψ : dA × dB → ℂ) (M : X → POVM A dA)
--       (U : X → I → Matrix dA dA ℂ) (V : X → J → Matrix dA dA ℂ)
--       (W : X → J → Matrix dB dB ℂ)
--       (hU : ∀ x i, (U x i)ᴴ * U x i = 1) (hW : ∀ x j, (W x j)ᴴ * W x j = 1) :
--       (∑ x, D x * ∑ i, μ x i * ∑ j, ν x j * ∑ a,
--         stateSqNorm ψ (((M x).mats a).val * (U x i * V x j) -
--           (U x i * V x j) * ((M x).mats a).val)) ≤
--         4 * (∑ x, D x * ∑ i, μ x i * ∑ a,
--           stateSqNorm ψ (((M x).mats a).val * U x i - U x i * ((M x).mats a).val)) +
--         4 * (∑ x, D x * ∑ j, ν x j * ∑ a,
--           stateSqNorm ψ (((M x).mats a).val * V x j - V x j * ((M x).mats a).val)) +
--         8 * (∑ x, D x * ∑ j, ν x j * xSqNorm ψ (V x j) (W x j))
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.two_sided_commutation_avg` is declared in `MIPRE/Foundations/Introspection/TwoSidedCommutation.lean`, lines 95–136. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TwoSidedCommutation.lean#L95-L136; blueprint lem:pauli-two-sided-commutation

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

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem MIPRE.Introspection.two_sided_commutation_avg {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (μ : X → I → ℝ) (ν : X → J → ℝ)
    (hμ0 : ∀ x i, 0 ≤ μ x i) (hν0 : ∀ x j, 0 ≤ ν x j)
    (hμ1 : ∀ x, ∑ i, μ x i = 1) (hν1 : ∀ x, ∑ j, ν x j = 1)
    (ψ : dA × dB → ℂ) (M : X → POVM A dA)
    (U : X → I → Matrix dA dA ℂ) (V : X → J → Matrix dA dA ℂ)
    (W : X → J → Matrix dB dB ℂ)
    (hU : ∀ x i, (U x i)ᴴ * U x i = 1) (hW : ∀ x j, (W x j)ᴴ * W x j = 1) :
    (∑ x, D x * ∑ i, μ x i * ∑ j, ν x j * ∑ a,
      stateSqNorm ψ (((M x).mats a).val * (U x i * V x j) -
        (U x i * V x j) * ((M x).mats a).val)) ≤
      4 * (∑ x, D x * ∑ i, μ x i * ∑ a,
        stateSqNorm ψ (((M x).mats a).val * U x i - U x i * ((M x).mats a).val)) +
      4 * (∑ x, D x * ∑ j, ν x j * ∑ a,
        stateSqNorm ψ (((M x).mats a).val * V x j - V x j * ((M x).mats a).val)) +
      8 * (∑ x, D x * ∑ j, ν x j * xSqNorm ψ (V x j) (W x j)) := by sorry
