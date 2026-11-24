-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Count_one_dim_nat
-- name    : GlobalTheory.CompanionTheory.Count.one_dim_nat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:33:54.436876+00:00
-- url     : https://prove2.me/theorems/19facb1e-610d-448c-aa57-e91fcfca62dd
-- title:
--   Count: one dim nat
-- statement:
--   The Count construction uses the one dim nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeSumDecayBound.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeSumDecayBound.lean#L33-L41

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MultiDimensional
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeSumDecayBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Count

theorem GlobalTheory.CompanionTheory.Count.one_dim_nat (b : ℝ) (hb : 0 < b) :
    ∑' k : ℕ, ENNReal.ofReal (((1 + ((k : ℝ) + 1) / b) ^ 2)⁻¹) ≤ ENNReal.ofReal b := by sorry
