-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_local_unit_of_dvr_unit
-- name    : GlobalTheory.T.exists_local_unit_of_dvr_unit
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:54.686805+00:00
-- url     : https://prove2.me/theorems/162b3c23-299f-596c-8d7d-4fe5c5ccd620
-- title:
--   T: exists local unit of dvr unit
-- statement:
--   The T construction uses the exists local unit of dvr unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitOfDvrUnitStatement.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitOfDvrUnitStatement.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitOfDvrUnit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitOfDvrUnitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_local_unit_of_dvr_unit : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] (𝔭 : PrimeSpectrum A),
    𝔭.asIdeal.height = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (iT : Localization.AtPrime 𝔭.asIdeal →+* V), Function.Injective iT → IsLocalHom iT → ∀ a b : A,
    (∃ w : Vˣ, iT (algebraMap A _ a) = iT (algebraMap A _ b) * w) →
    ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ, (u : Localization.AtPrime 𝔭.asIdeal) * algebraMap A _ b = algebraMap A _ a := by sorry
