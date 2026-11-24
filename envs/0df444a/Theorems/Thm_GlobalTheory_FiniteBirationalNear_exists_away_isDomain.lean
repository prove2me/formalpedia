-- Prove2me | Theorems.Thm_GlobalTheory_FiniteBirationalNear_exists_away_isDomain
-- name    : GlobalTheory.FiniteBirationalNear.exists_away_isDomain
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:29:57.944799+00:00
-- url     : https://prove2.me/theorems/28f871ab-aa4e-4b2a-b715-7b6888dbb741
-- title:
--   Finite Birational Near: exists away is Domain
-- statement:
--   The Finite Birational Near construction uses the exists away is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoNearNormalPointOfFiniteBirational.lean#L21-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoNearNormalPointOfFiniteBirational.lean#L21-L42

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

theorem GlobalTheory.FiniteBirationalNear.exists_away_isDomain {A O : Type*} [CommRing A] [IsNoetherianRing A] [CommRing O]
    [Algebra A O] (S : Submonoid A) [IsLocalization S O] [IsDomain O] :
    ∃ s ∈ S, ∀ (P : Type) [CommRing P] [Algebra A P] [IsLocalization.Away s P], IsDomain P := by sorry
