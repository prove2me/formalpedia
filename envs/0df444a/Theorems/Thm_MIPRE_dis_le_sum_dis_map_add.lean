-- Prove2me | Theorems.Thm_MIPRE_dis_le_sum_dis_map_add
-- name    : MIPRE.dis_le_sum_dis_map_add
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:56.635037+00:00
-- url     : https://prove2.me/theorems/eb546bd6-2902-431f-9833-e7af75795846
-- title:
--   From evaluations to outcomes: when distinct outcomes are separated by an evaluation map at a point drawn from ν, colliding with probability at most ε, the disagreement of…
-- statement:
--   A statement of the module `MIPRE.Foundations.Disagreement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The disagreement of two parties' measurements. The probability `dis ψ M N = 1 - ∑_a ⟨ψ| M_a ⊗ N_a |ψ⟩` that Alice's POVM `M` and Bob's `N`, measured on `ψ`, return different outcomes, and four facts about it that the soundness of answer reduction uses throughout: * it only decreases under a common coarse-graining (`dis_map_le`); * disagreements chain across the two parties, linearly (`sum_dis_triangle`, from `agreeSum_triangle`): Alice's `A` against Bob's `D` through Bob's `B` and Alice's `C`; * the probability of an event under Alice's measurement is at most its probability under Bob's, plus…
--
--   **From evaluations to outcomes**: when distinct outcomes are separated by an evaluation map at
--   a point drawn from `ν`, colliding with probability at most `ε`, the disagreement of the outcomes is
--   at most the average disagreement of the evaluations, plus `ε`. Neither measurement need be
--   projective.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped Kronecker
--   variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
--
--   theorem MIPRE.dis_le_sum_dis_map_add {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) [DecidableEq Λ]
--       (M : POVM Λ dA) (N : POVM Λ dB) {Y R : Type*} [Fintype Y] [Fintype R] [DecidableEq R]
--       {ν : Y → ℝ} (hν0 : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (ev : Y → Λ → R) {ε : ℝ}
--       (hε : 0 ≤ ε)
--       (hsep : ∀ g g', g ≠ g' → ∑ y, ν y * (if ev y g = ev y g' then 1 else 0) ≤ ε) :
--       dis ψ M N ≤ ∑ y, ν y * dis ψ (M.map (ev y)) (N.map (ev y)) + ε
--   ```
--
--   **Formalization Note** `MIPRE.dis_le_sum_dis_map_add` is declared in `MIPRE/Foundations/Disagreement.lean`, lines 189–258. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Disagreement.lean#L189-L258

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

theorem MIPRE.dis_le_sum_dis_map_add {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) [DecidableEq Λ]
    (M : POVM Λ dA) (N : POVM Λ dB) {Y R : Type*} [Fintype Y] [Fintype R] [DecidableEq R]
    {ν : Y → ℝ} (hν0 : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (ev : Y → Λ → R) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsep : ∀ g g', g ≠ g' → ∑ y, ν y * (if ev y g = ev y g' then 1 else 0) ≤ ε) :
    dis ψ M N ≤ ∑ y, ν y * dis ψ (M.map (ev y)) (N.map (ev y)) + ε := by sorry
