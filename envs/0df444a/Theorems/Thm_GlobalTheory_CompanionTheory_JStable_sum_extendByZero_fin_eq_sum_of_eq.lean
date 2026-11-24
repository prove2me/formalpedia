-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_JStable_sum_extendByZero_fin_eq_sum_of_eq
-- name    : GlobalTheory.CompanionTheory.JStable.sum_extendByZero_fin_eq_sum_of_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:46.568252+00:00
-- url     : https://prove2.me/theorems/68d61475-4f18-4e04-94d9-2f00604dc7bc
-- title:
--   JStable: sum extend By Zero fin eq sum of eq
-- statement:
--   The JStable construction uses the sum extend By Zero fin eq sum of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspace.lean#L75-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspace.lean#L75-L88

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

theorem GlobalTheory.CompanionTheory.JStable.sum_extendByZero_fin_eq_sum_of_eq (s : Bool) (x y : EuclideanSpace ℂ {i : Fin n // ε i = s}) :
    ∑ a, star (ext0 ε s x a) * ext0 ε s y a = inner ℂ x y := by sorry
