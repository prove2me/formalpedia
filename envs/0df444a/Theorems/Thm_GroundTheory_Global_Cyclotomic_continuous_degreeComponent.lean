-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_degreeComponent
-- name    : GroundTheory.Global.Cyclotomic.continuous_degreeComponent
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:16.89524+00:00
-- url     : https://prove2.me/theorems/066789be-9ae8-4549-8f8e-fe6020e04fe5
-- title:
--   Cyclotomic: continuous degree Component
-- statement:
--   The Cyclotomic construction uses the continuous degree Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L107-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L107-L111

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

theorem GroundTheory.Global.Cyclotomic.continuous_degreeComponent (q : Nat.Primes) : Continuous (degreeComponent q) := by sorry
