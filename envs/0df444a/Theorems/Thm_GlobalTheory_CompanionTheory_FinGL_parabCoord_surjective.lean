-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_parabCoord_surjective
-- name    : GlobalTheory.CompanionTheory.FinGL.parabCoord_surjective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:39:20.463194+00:00
-- url     : https://prove2.me/theorems/5bc87261-4a2c-454e-83fa-61899d7a1844
-- title:
--   Fin GL: parab Coord surjective
-- statement:
--   The Fin GL construction uses the parab Coord surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L83-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L83-L118

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

theorem GlobalTheory.CompanionTheory.FinGL.parabCoord_surjective : Function.Surjective (parabCoord K b) := by sorry
