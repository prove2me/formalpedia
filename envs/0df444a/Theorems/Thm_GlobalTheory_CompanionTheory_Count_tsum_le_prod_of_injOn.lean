-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Count_tsum_le_prod_of_injOn
-- name    : GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:33:51.402686+00:00
-- url     : https://prove2.me/theorems/47e33a61-239a-4737-9693-a0889eaa257d
-- title:
--   Count: tsum le prod of inj On
-- statement:
--   The Count construction uses the tsum le prod of inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeSumDecayBound.lean#L85-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeSumDecayBound.lean#L85-L102

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

theorem GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn {S P : Type} [Fintype P] (m : S → P → ℤ) (b : P → ℝ)
    (hb : ∀ p, 0 < b p) (h : S → ℝ≥0∞) (hinj : Set.InjOn m {ξ | h ξ ≠ 0})
    (hh : ∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹)) :
    ∑' ξ, h ξ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) := by sorry
