-- Prove2me | Theorems.Thm_GlobalTheory_GroupAlg_finrank_of_injective
-- name    : GlobalTheory.GroupAlg.finrank_of_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:57:37.202798+00:00
-- url     : https://prove2.me/theorems/970491bc-2b0c-4d0d-96a8-62712983eaed
-- title:
--   Group Alg: finrank of injective
-- statement:
--   The Group Alg construction uses the finrank of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinitePresentationOfInjective.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinitePresentationOfInjective.lean#L108-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.GroupAlg
variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)

theorem GlobalTheory.GroupAlg.finrank_of_injective (hu : Function.Injective u) [u.range.FiniteIndex]
    (p : PrimeSpectrum R[Y]) : (mapDomainRingHom R u).finrank p = u.range.index := by sorry
