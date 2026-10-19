-- Prove2me | Theorems.Thm_MIPRE_Introspection_commutator_product_bound
-- name    : MIPRE.Introspection.commutator_product_bound
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:11:38.068994+00:00
-- url     : https://prove2.me/theorems/6a125a28-6997-4267-92d8-f2332affdcf7
-- title:
--   The four-link commutation argument, with an arbitrary commuting mirror W
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.TwoSidedCommutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Combining approximate commutations across a bipartite state. Transfer the second unitary to the other party, commute the first, and transfer back. The POVM square-sum bound controls both transfer errors without an alphabet factor.
--
--   The four-link commutation argument, with an arbitrary commuting mirror `W`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]
--
--   theorem MIPRE.Introspection.commutator_product_bound (ψ : N → ℂ) (M : A → Matrix N N ℂ)
--       (hM : ∑ a, (M a)ᴴ * M a ≤ (1 : Matrix N N ℂ))
--       (U V W : Matrix N N ℂ) (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1)
--       (hWU : W * U = U * W) (hWM : ∀ a, W * M a = M a * W) :
--       (∑ a, snorm ψ (M a * (U * V) - (U * V) * M a) ^ 2) ≤
--         4 * (∑ a, snorm ψ (M a * U - U * M a) ^ 2) +
--         4 * (∑ a, snorm ψ (M a * V - V * M a) ^ 2) +
--         8 * snorm ψ (V - W) ^ 2
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.commutator_product_bound` is declared in `MIPRE/Foundations/Introspection/TwoSidedCommutation.lean`, lines 22–76. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TwoSidedCommutation.lean#L22-L76; blueprint lem:pauli-two-sided-commutation

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

theorem MIPRE.Introspection.commutator_product_bound (ψ : N → ℂ) (M : A → Matrix N N ℂ)
    (hM : ∑ a, (M a)ᴴ * M a ≤ (1 : Matrix N N ℂ))
    (U V W : Matrix N N ℂ) (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1)
    (hWU : W * U = U * W) (hWM : ∀ a, W * M a = M a * W) :
    (∑ a, snorm ψ (M a * (U * V) - (U * V) * M a) ^ 2) ≤
      4 * (∑ a, snorm ψ (M a * U - U * M a) ^ 2) +
      4 * (∑ a, snorm ψ (M a * V - V * M a) ^ 2) +
      8 * snorm ψ (V - W) ^ 2 := by sorry
