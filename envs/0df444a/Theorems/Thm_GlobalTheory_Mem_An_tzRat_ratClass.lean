-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_tzRat_ratClass
-- name    : GlobalTheory.Mem.An.tzRat_ratClass
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:50:53.556807+00:00
-- url     : https://prove2.me/theorems/de90e8c5-dd6b-4c60-9330-c1dae277a62d
-- title:
--   An: tz Rat rat Class
-- statement:
--   The An construction uses the tz Rat rat Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimesAPIntervalOfTzRat.lean#L112-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimesAPIntervalOfTzRat.lean#L112-L143

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimesAPIntervalOfTzRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An

theorem GlobalTheory.Mem.An.tzRat_ratClass (h : TZRat) :
    ∃ C₀ Cr cr cb : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < cb ∧ Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions C₀ Cr cr cb := by sorry
