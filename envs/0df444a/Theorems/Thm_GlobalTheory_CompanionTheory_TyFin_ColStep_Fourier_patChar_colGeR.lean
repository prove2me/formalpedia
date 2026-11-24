-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Fourier_patChar_colGeR
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.patChar_colGeR
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:12.731657+00:00
-- url     : https://prove2.me/theorems/bb437b20-e9be-45cb-83a2-852c4fff1f5e
-- title:
--   Fourier: pat Char col Ge R
-- statement:
--   The Fourier construction uses the pat Char col Ge R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerColumnRecursion.lean#L49-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerColumnRecursion.lean#L49-L64

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

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.patChar_colGeR {d j : ℕ} (hj : j < d) (r : Fin j → K) (ψ₀ : AddChar K ℂ) (u : GL (Fin d) K) :
    patChar (colGeR K d j r) ψ₀ u =
      patChar (colGeE K d (j + 1)) ψ₀ u * ψ₀ (∑ i, r i * colEntries hj u i) := by sorry
