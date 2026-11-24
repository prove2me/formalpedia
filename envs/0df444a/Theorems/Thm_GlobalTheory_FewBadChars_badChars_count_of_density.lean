-- Prove2me | Theorems.Thm_GlobalTheory_FewBadChars_badChars_count_of_density
-- name    : GlobalTheory.FewBadChars.badChars_count_of_density
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:13.71022+00:00
-- url     : https://prove2.me/theorems/36938e69-e1e2-486b-8181-b1aab9576e8e
-- title:
--   Few Bad Chars: bad Chars count of density
-- statement:
--   The Few Bad Chars construction uses the bad Chars count of density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/BadCharsCountOfDensity.lean#L10-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/BadCharsCountOfDensity.lean#L10-L49

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__Jutila_fbdb89691f60b7b2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_BadCharsCountOfDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FewBadChars
open Formalism.HermitianLattices.GL2PrimeSums

theorem GlobalTheory.FewBadChars.badChars_count_of_density : GlobalTheory.Mem.An.Jutila → ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
    (((Formalism.HermitianLattices.GL2PrimeSums.BadChars Q).encard : ℕ∞) : ENNReal) ≤ ENNReal.ofReal (C * Q ^ ((1 : ℝ) / 4)) := by sorry
