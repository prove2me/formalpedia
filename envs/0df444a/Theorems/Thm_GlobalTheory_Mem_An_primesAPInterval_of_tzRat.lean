-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_primesAPInterval_of_tzRat
-- name    : GlobalTheory.Mem.An.primesAPInterval_of_tzRat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:25.973975+00:00
-- url     : https://prove2.me/theorems/2cca58dd-c3e7-410d-bf7e-2ae89f68e63f
-- title:
--   An: primes APInterval of tz Rat
-- statement:
--   The An construction uses the primes APInterval of tz Rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimesAPIntervalOfTzRat.lean#L145-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimesAPIntervalOfTzRat.lean#L145-L150

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

theorem GlobalTheory.Mem.An.primesAPInterval_of_tzRat (h : TZRat) :
    ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ PrimesAPInterval C₀ Cr cr c := by sorry
