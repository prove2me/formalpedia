-- Prove2me | Theorems.Thm_GlobalTheory_GroupAlg_surjective_of_surjective
-- name    : GlobalTheory.GroupAlg.surjective_of_surjective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:57:36.40801+00:00
-- url     : https://prove2.me/theorems/f033dd04-4cfb-49b1-bee8-4d840f4c3267
-- title:
--   Group Alg: surjective of surjective
-- statement:
--   The Group Alg construction uses the surjective of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinitePresentationOfInjective.lean#L118-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinitePresentationOfInjective.lean#L118-L129

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

theorem GlobalTheory.GroupAlg.surjective_of_surjective (hu : Function.Surjective u) :
    Function.Surjective (mapDomainRingHom R u) := by sorry
