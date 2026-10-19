-- Prove2me | Theorems.Thm_MIPRE_condFail_le_of
-- name    : MIPRE.condFail_le_of
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:28.378461+00:00
-- url     : https://prove2.me/theorems/c2fda6ef-35eb-4bf6-b99d-c7a9a3c2fbc2
-- title:
--   A subtest accepting when two events are avoided and two readings agree fails at most the events' probabilities plus the readings' disagreement
-- statement:
--   A statement of the module `MIPRE.Foundations.Disagreement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The disagreement of two parties' measurements. The probability `dis ψ M N = 1 - ∑_a ⟨ψ| M_a ⊗ N_a |ψ⟩` that Alice's POVM `M` and Bob's `N`, measured on `ψ`, return different outcomes, and four facts about it that the soundness of answer reduction uses throughout: * it only decreases under a common coarse-graining (`dis_map_le`); * disagreements chain across the two parties, linearly (`sum_dis_triangle`, from `agreeSum_triangle`): Alice's `A` against Bob's `D` through Bob's `B` and Alice's `C`; * the probability of an event under Alice's measurement is at most its probability under Bob's, plus…
--
--   **A subtest accepting when two events are avoided and two readings agree** fails at most the
--   events' probabilities plus the readings' disagreement.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped Kronecker
--   variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
--   variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
--
--   theorem MIPRE.condFail_le_of (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (EA : A → Prop) (EB : B → Prop)
--       [DecidablePred EA] [DecidablePred EB] (f : A → C) (g : B → C)
--       (hD : ∀ a b, ¬ EA a → ¬ EB b → f a = g b → G.D x y a b = true) :
--       condFail G ψ MA MB x y
--         ≤ ∑ a, (if EA a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
--           + ∑ b, (if EB b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
--           + dis ψ ((MA x).map f) ((MB y).map g)
--   ```
--
--   **Formalization Note** `MIPRE.condFail_le_of` is declared in `MIPRE/Foundations/Disagreement.lean`, lines 395–459. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Disagreement.lean#L395-L459

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_Disagreement

open MIPRE
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}

theorem MIPRE.condFail_le_of (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (EA : A → Prop) (EB : B → Prop)
    [DecidablePred EA] [DecidablePred EB] (f : A → C) (g : B → C)
    (hD : ∀ a b, ¬ EA a → ¬ EB b → f a = g b → G.D x y a b = true) :
    condFail G ψ MA MB x y
      ≤ ∑ a, (if EA a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
        + ∑ b, (if EB b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
        + dis ψ ((MA x).map f) ((MB y).map g) := by sorry
