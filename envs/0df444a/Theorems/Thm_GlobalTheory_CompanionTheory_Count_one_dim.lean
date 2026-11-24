-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Count_one_dim
-- name    : GlobalTheory.CompanionTheory.Count.one_dim
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:43.293947+00:00
-- url     : https://prove2.me/theorems/79236999-cbfd-46aa-a3b0-b1bfa4e7887c
-- title:
--   Count: one dim
-- statement:
--   The Count construction uses the one dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeSumDecayBound.lean#L43-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeSumDecayBound.lean#L43-L79

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

theorem GlobalTheory.CompanionTheory.Count.one_dim (b : ℝ) (hb : 0 < b) :
    ∑' n : ℤ, ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) ≤ ENNReal.ofReal (1 + 2 * b) := by sorry
