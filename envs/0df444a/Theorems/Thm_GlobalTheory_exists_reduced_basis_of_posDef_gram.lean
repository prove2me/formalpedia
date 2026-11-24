-- Prove2me | Theorems.Thm_GlobalTheory_exists_reduced_basis_of_posDef_gram
-- name    : GlobalTheory.exists_reduced_basis_of_posDef_gram
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:41:04.485142+00:00
-- url     : https://prove2.me/theorems/76a8a1b5-a792-42d8-a503-0698976a117e
-- title:
--   Global Theory: exists reduced basis of pos Def gram
-- statement:
--   The Global Theory construction uses the exists reduced basis of pos Def gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L175-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L175-L190

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module Matrix
open scoped InnerProductSpace TensorProduct MatrixOrder ComplexOrder
open GlobalTheory
open ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2 ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
variable {X : Type*} [AddCommGroup X] {d : ℕ}

theorem GlobalTheory.exists_reduced_basis_of_posDef_gram (q : QuadraticMap ℤ X ℝ) (b : Basis (Fin d) ℤ X)
    (hq : (Matrix.of fun i j => QuadraticMap.polar q (b i) (b j)).PosDef) :
    ∃ e : Basis (Fin d) ℤ X,
      (∀ (i : Fin d) (μ : X), |QuadraticMap.polar q (e i) μ| ≤
        (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) * QuadraticMap.polar q μ μ) ∧
      ∀ N : ℤ, 1 ≤ N → ∀ α : X, (∀ w : X, q α ≤ q (α + N • w)) → ∀ i : Fin d,
        |(e.repr α i : ℝ)| ≤ (d : ℝ) * (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * N := by sorry
