-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_JStable_extendByZero_restrict_eigen_projection
-- name    : GlobalTheory.CompanionTheory.JStable.extendByZero_restrict_eigen_projection
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:04:01.976808+00:00
-- url     : https://prove2.me/theorems/03112a15-5e67-4d4d-a6f4-27cf60c72788
-- title:
--   JStable: extend By Zero restrict eigen projection
-- statement:
--   The JStable construction uses the extend By Zero restrict eigen projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspace.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspace.lean#L60-L67

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

theorem GlobalTheory.CompanionTheory.JStable.extendByZero_restrict_eigen_projection (s : Bool) (v : Fin n → ℂ) :
    ext0 ε s (res0 ε s v) =
      (1 / 2 : ℂ) • (v + (if s then (1 : ℂ) else -1) • (Formalism.REAL.Jm ε *ᵥ v)) := by sorry
