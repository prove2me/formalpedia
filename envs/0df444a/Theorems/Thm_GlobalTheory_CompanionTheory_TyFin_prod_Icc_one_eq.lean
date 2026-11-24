-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_prod_Icc_one_eq
-- name    : GlobalTheory.CompanionTheory.TyFin.prod_Icc_one_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:09:29.340519+00:00
-- url     : https://prove2.me/theorems/590ce7ef-4391-4ee9-bc60-5fd1ed0521e8
-- title:
--   Ty Fin: prod Icc one eq
-- statement:
--   The Ty Fin construction uses the prod Icc one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquarefreeDimensionFormula.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquarefreeDimensionFormula.lean#L10-L16

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraDimensionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquarefreeDimensionFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin

theorem GlobalTheory.CompanionTheory.TyFin.prod_Icc_one_eq (f : ℕ → ℤ) (d : ℕ) (h : 1 ≤ d) :
    ∏ i ∈ Finset.Icc 1 d, f i = (∏ i ∈ Finset.Ico 1 d, f i) * f d := by sorry
