-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_fixingSubgroup_zhatField
-- name    : GroundTheory.Global.Cyclotomic.fixingSubgroup_zhatField
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:19.985866+00:00
-- url     : https://prove2.me/theorems/1005fc76-092d-53b6-8998-89d92a2f58ff
-- title:
--   Cyclotomic: fixing Subgroup zhat Field
-- statement:
--   The Cyclotomic construction uses the fixing Subgroup zhat Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L170-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L170-L171

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

theorem GroundTheory.Global.Cyclotomic.fixingSubgroup_zhatField : zhatField.fixingSubgroup = degree.ker := by sorry
