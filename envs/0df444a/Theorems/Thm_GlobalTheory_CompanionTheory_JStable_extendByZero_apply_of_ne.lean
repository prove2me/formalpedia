-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_JStable_extendByZero_apply_of_ne
-- name    : GlobalTheory.CompanionTheory.JStable.extendByZero_apply_of_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:16.931603+00:00
-- url     : https://prove2.me/theorems/d53be21d-d436-4587-be3c-9573b065cf64
-- title:
--   JStable: extend By Zero apply of ne
-- statement:
--   The JStable construction uses the extend By Zero apply of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspace.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspace.lean#L56-L58

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

theorem GlobalTheory.CompanionTheory.JStable.extendByZero_apply_of_ne {s : Bool} (x : EuclideanSpace ℂ {i : Fin n // ε i = s}) {a : Fin n}
    (h : ε a ≠ s) : ext0 ε s x a = 0 := by sorry
