-- Prove2me | Theorems.Thm_MIPRE_sum_ite_bornProb_le_condFail
-- name    : MIPRE.sum_ite_bornProb_le_condFail
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:04.382307+00:00
-- url     : https://prove2.me/theorems/5727be6c-e015-49ae-8d3a-a89be7b6a576
-- title:
--   A subtest excluding an event of Bob's answer bounds its probability
-- statement:
--   A statement of the module `MIPRE.Foundations.Disagreement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The disagreement of two parties' measurements. The probability `dis ψ M N = 1 - ∑_a ⟨ψ| M_a ⊗ N_a |ψ⟩` that Alice's POVM `M` and Bob's `N`, measured on `ψ`, return different outcomes, and four facts about it that the soundness of answer reduction uses throughout: * it only decreases under a common coarse-graining (`dis_map_le`); * disagreements chain across the two parties, linearly (`sum_dis_triangle`, from `agreeSum_triangle`): Alice's `A` against Bob's `D` through Bob's `B` and Alice's `C`; * the probability of an event under Alice's measurement is at most its probability under Bob's, plus…
--
--   **A subtest excluding an event of Bob's answer bounds its probability.**
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
--   theorem MIPRE.sum_ite_bornProb_le_condFail (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (E : B → Prop)
--       [DecidablePred E] (hD : ∀ a b, G.D x y a b = true → ¬ E b) :
--       ∑ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
--         ≤ condFail G ψ MA MB x y
--   ```
--
--   **Formalization Note** `MIPRE.sum_ite_bornProb_le_condFail` is declared in `MIPRE/Foundations/Disagreement.lean`, lines 315–346. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Disagreement.lean#L315-L346

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

theorem MIPRE.sum_ite_bornProb_le_condFail (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (E : B → Prop)
    [DecidablePred E] (hD : ∀ a b, G.D x y a b = true → ¬ E b) :
    ∑ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
      ≤ condFail G ψ MA MB x y := by sorry
