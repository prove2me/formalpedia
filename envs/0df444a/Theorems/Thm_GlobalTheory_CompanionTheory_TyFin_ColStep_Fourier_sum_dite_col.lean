-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Fourier_sum_dite_col
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.sum_dite_col
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:00.441126+00:00
-- url     : https://prove2.me/theorems/98d28e50-70b6-4e38-9271-8a5c872a10f1
-- title:
--   Fourier: sum dite col
-- statement:
--   The Fourier construction uses the sum dite col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerColumnRecursion.lean#L16-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerColumnRecursion.lean#L16-L47

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerColumnRecursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.sum_dite_col {d j : ℕ} (hj : j < d) (r : Fin j → K) (M : Matrix (Fin d) (Fin d) K) :
    ∑ i : Fin d, ∑ l : Fin d, (if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0) * M i l =
      ∑ i : Fin j, r i * M ⟨i, i.2.trans hj⟩ ⟨j, hj⟩ := by sorry
