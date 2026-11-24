-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_JStable_exists_adapted_onb
-- name    : GlobalTheory.CompanionTheory.JStable.exists_adapted_onb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:52.210586+00:00
-- url     : https://prove2.me/theorems/db2ff0ef-9c27-444a-8f06-2277c708ecba
-- title:
--   JStable: exists adapted onb
-- statement:
--   The JStable construction uses the exists adapted onb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspace.lean#L12-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspace.lean#L12-L40

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
open Module

theorem GlobalTheory.CompanionTheory.JStable.exists_adapted_onb {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) :
    ∃ (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (T : Set ι),
      W = Submodule.span ℂ (b '' T) := by sorry
