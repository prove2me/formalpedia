-- Prove2me | Theorems.Thm_GlobalTheory_toUnits_unitaryCharToCircle
-- name    : GlobalTheory.toUnits_unitaryCharToCircle
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:39.599305+00:00
-- url     : https://prove2.me/theorems/f91ad221-6085-4783-9976-32a7f9873b4d
-- title:
--   Global Theory: to Units unitary Char To Circle
-- statement:
--   The Global Theory construction uses the to Units unitary Char To Circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUnitaryCharOfOpenSubgroupAndHom.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUnitaryCharOfOpenSubgroupAndHom.lean#L16-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsContinuousCircleCharExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory

theorem GlobalTheory.toUnits_unitaryCharToCircle {A : Type} [CommGroup A] (a : A →* ℂˣ)
    (ha : ∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) (y : A) :
    Circle.toUnits (unitaryCharToCircle a ha y) = a y := by sorry
