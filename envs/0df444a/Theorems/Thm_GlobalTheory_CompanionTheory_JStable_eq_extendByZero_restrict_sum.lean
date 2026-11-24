-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_JStable_eq_extendByZero_restrict_sum
-- name    : GlobalTheory.CompanionTheory.JStable.eq_extendByZero_restrict_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:58:38.645278+00:00
-- url     : https://prove2.me/theorems/3738981f-98a5-4c85-a66b-a65f984a9ecc
-- title:
--   JStable: eq extend By Zero restrict sum
-- statement:
--   The JStable construction uses the eq extend By Zero restrict sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspace.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspace.lean#L69-L73

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsOrthogonalHermitianSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.JStable
variable {n : ℕ} (ε : Fin n → Bool)

theorem GlobalTheory.CompanionTheory.JStable.eq_extendByZero_restrict_sum (v : Fin n → ℂ) :
    v = ext0 ε true (res0 ε true v) + ext0 ε false (res0 ε false v) := by sorry
