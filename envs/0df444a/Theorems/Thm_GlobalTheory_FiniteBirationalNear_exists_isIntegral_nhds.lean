-- Prove2me | Theorems.Thm_GlobalTheory_FiniteBirationalNear_exists_isIntegral_nhds
-- name    : GlobalTheory.FiniteBirationalNear.exists_isIntegral_nhds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:29:52.710318+00:00
-- url     : https://prove2.me/theorems/71746f40-a4ca-4b6d-96de-1e6a8771ba59
-- title:
--   Finite Birational Near: exists is Integral nhds
-- statement:
--   The Finite Birational Near construction uses the exists is Integral nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoNearNormalPointOfFiniteBirational.lean#L72-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoNearNormalPointOfFiniteBirational.lean#L72-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoNearNormalPointOfFiniteBirational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open GlobalTheory GlobalTheory.FiniteBirationalNear

theorem GlobalTheory.FiniteBirationalNear.exists_isIntegral_nhds {M : Scheme.{0}} [IsLocallyNoetherian M] (x : M)
    [IsDomain (M.presheaf.stalk x)] : ∃ V : M.Opens, x ∈ V ∧ IsIntegral V := by sorry
