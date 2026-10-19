-- Prove2me | Theorems.Thm_MIPRE_sum_ite_bornProb_le_condFail_prime
-- name    : MIPRE.sum_ite_bornProb_le_condFail_prime
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:05.519225+00:00
-- url     : https://prove2.me/theorems/72a4912f-15b6-46d2-b3c1-164e02a20e6a
-- title:
--   The mirror image, for an event of Alice's answer
-- statement:
--   A statement of the module `MIPRE.Foundations.Disagreement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The disagreement of two parties' measurements. The probability `dis ψ M N = 1 - ∑_a ⟨ψ| M_a ⊗ N_a |ψ⟩` that Alice's POVM `M` and Bob's `N`, measured on `ψ`, return different outcomes, and four facts about it that the soundness of answer reduction uses throughout: * it only decreases under a common coarse-graining (`dis_map_le`); * disagreements chain across the two parties, linearly (`sum_dis_triangle`, from `agreeSum_triangle`): Alice's `A` against Bob's `D` through Bob's `B` and Alice's `C`; * the probability of an event under Alice's measurement is at most its probability under Bob's, plus…
--
--   The mirror image, for an event of Alice's answer.
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
--   theorem MIPRE.sum_ite_bornProb_le_condFail_prime (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (E : A → Prop)
--       [DecidablePred E] (hD : ∀ a b, G.D x y a b = true → ¬ E a) :
--       ∑ a, (if E a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
--         ≤ condFail G ψ MA MB x y
--   ```
--
--   **Formalization Note** `MIPRE.sum_ite_bornProb_le_condFail_prime` is declared in `MIPRE/Foundations/Disagreement.lean`, lines 348–376. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository (there named `MIPRE.sum_ite_bornProb_le_condFail'`; renamed for the platform, which requires ASCII identifiers). The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Disagreement.lean#L348-L376

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

theorem MIPRE.sum_ite_bornProb_le_condFail_prime (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (E : A → Prop)
    [DecidablePred E] (hD : ∀ a b, G.D x y a b = true → ¬ E a) :
    ∑ a, (if E a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
      ≤ condFail G ψ MA MB x y := by sorry
