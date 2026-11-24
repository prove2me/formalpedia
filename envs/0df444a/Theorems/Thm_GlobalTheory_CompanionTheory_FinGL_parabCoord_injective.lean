-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_parabCoord_injective
-- name    : GlobalTheory.CompanionTheory.FinGL.parabCoord_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:39:43.779278+00:00
-- url     : https://prove2.me/theorems/a1af392e-aea4-472a-8da2-6204d806f5f9
-- title:
--   Fin GL: parab Coord injective
-- statement:
--   The Fin GL construction uses the parab Coord injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L70-L81

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGL
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)

theorem GlobalTheory.CompanionTheory.FinGL.parabCoord_injective : Function.Injective (parabCoord K b) := by sorry
