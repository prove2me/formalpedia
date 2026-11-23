-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_HasAdj_mul
-- name    : GlobalTheory.CompanionTheory.CapelliAdj.HasAdj.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:13.79934+00:00
-- url     : https://prove2.me/theorems/88adf7cd-e4d4-49a3-afe6-506c5dac4df0
-- title:
--   Has Adj: mul
-- statement:
--   The Has Adj construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetAdjointForm.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetAdjointForm.lean#L13-L17

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNegStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetAdjointForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliAdj
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.CapelliAdj.HasAdj.mul {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {T T' S S' : Module.End ℂ V}
    (h : HasAdj B T S) (h' : HasAdj B T' S') : HasAdj B (T * T') (S' * S) := by sorry
