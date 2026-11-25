-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_traceDual_clear_by_integer
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.traceDual_clear_by_integer
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:48.568039+00:00
-- url     : https://prove2.me/theorems/546a8e5e-60df-4463-ba62-d5f8441ecf00
-- title:
--   Integ: trace Dual clear by integer
-- statement:
--   The Integ construction uses the trace Dual clear by integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TraceDualDenominatorBounded.lean#L6-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TraceDualDenominatorBounded.lean#L6-L28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TraceDualDenominatorBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.traceDual_clear_by_integer : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ f : F,
    (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f := by sorry
