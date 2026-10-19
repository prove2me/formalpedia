-- Prove2me | Theorems.Thm_MIPRE_Introspection_hiding_chain_average
-- name    : MIPRE.Introspection.hiding_chain_average
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:10:17.433194+00:00
-- url     : https://prove2.me/theorems/d892417a-e49a-4fb0-a490-9641e0e511be
-- title:
--   The averaged hiding chain, with one error bound per edge and no dependence on the number of outcomes or sampled question seeds
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.HidingTests` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Hiding-test chains after coarse-graining consistency. Coarse-graining is performed on the tests' accepted-answer relations. Only then are the two cross-party estimates combined into a same-side estimate. This is the order required to avoid the exponentially large fibre loss discussed in the paper's corrected proof of `lem:intro-sound-2`.
--
--   The averaged hiding chain, with one error bound per edge and no dependence on the
--   number of outcomes or sampled question seeds.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Classical
--   variable {X Y A B C J H K : Type*}
--
--   theorem MIPRE.Introspection.hiding_chain_average (ψ : H × K → ℂ) (D : J → ℝ) (hD : ∀ j, 0 ≤ D j)
--       (P : ℕ → J → C → Matrix H H ℂ) (n : ℕ) (δ : ℕ → ℝ)
--       (hstep : ∀ i < n, (∑ j, D j * ∑ z, stateSqNorm ψ (P i j z - P (i + 1) j z)) ≤ δ i) :
--       (∑ j, D j * ∑ z, stateSqNorm ψ (P 0 j z - P n j z)) ≤
--         (n : ℝ) * ∑ i ∈ Finset.range n, δ i
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.hiding_chain_average` is declared in `MIPRE/Foundations/Introspection/HidingTests.lean`, lines 97–119. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HidingTests.lean#L97-L119; blueprint lem:intro-subtest-estimates

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
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
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix

open MIPRE
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {X Y A B C J H K : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
  [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

theorem MIPRE.Introspection.hiding_chain_average (ψ : H × K → ℂ) (D : J → ℝ) (hD : ∀ j, 0 ≤ D j)
    (P : ℕ → J → C → Matrix H H ℂ) (n : ℕ) (δ : ℕ → ℝ)
    (hstep : ∀ i < n, (∑ j, D j * ∑ z, stateSqNorm ψ (P i j z - P (i + 1) j z)) ≤ δ i) :
    (∑ j, D j * ∑ z, stateSqNorm ψ (P 0 j z - P n j z)) ≤
      (n : ℝ) * ∑ i ∈ Finset.range n, δ i := by sorry
