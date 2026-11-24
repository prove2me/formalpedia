-- Prove2me | Theorems.Thm_GlobalTheory_GroupAlg_finitePresentation_of_injective
-- name    : GlobalTheory.GroupAlg.finitePresentation_of_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:57:52.247537+00:00
-- url     : https://prove2.me/theorems/0fb3fbd3-a60a-4384-bfb2-3160ec53fda7
-- title:
--   Group Alg: finite Presentation of injective
-- statement:
--   The Group Alg construction uses the finite Presentation of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinitePresentationOfInjective.lean#L100-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinitePresentationOfInjective.lean#L100-L106

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

theorem GlobalTheory.GroupAlg.finitePresentation_of_injective (hu : Function.Injective u) [u.range.FiniteIndex] :
    (mapDomainRingHom R u).FinitePresentation := by sorry
