-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_degreeComponent_apply
-- name    : GroundTheory.Global.Cyclotomic.degreeComponent_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:12:38.344643+00:00
-- url     : https://prove2.me/theorems/96d30f81-9a80-4d30-8ba0-24f919614d93
-- title:
--   Cyclotomic: degree Component apply
-- statement:
--   The Cyclotomic construction uses the degree Component apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L98-L100

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped GroundTheory.LocalField.Abstract ComplexConjugate
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ

theorem GroundTheory.Global.Cyclotomic.degreeComponent_apply (q : Nat.Primes) (σ : Gal(ℚ̄/ℚ)) :
    degreeComponent q σ = padicUnitsLog q (Units.map (toPadicInt q).toMonoidHom (character σ)) := by sorry
