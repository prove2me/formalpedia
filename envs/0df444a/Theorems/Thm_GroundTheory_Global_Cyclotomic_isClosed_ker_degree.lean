-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_isClosed_ker_degree
-- name    : GroundTheory.Global.Cyclotomic.isClosed_ker_degree
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:17.345737+00:00
-- url     : https://prove2.me/theorems/c49f2453-c01f-4e80-b108-b9eebe53deda
-- title:
--   Cyclotomic: is Closed ker degree
-- statement:
--   The Cyclotomic construction uses the is Closed ker degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L167-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L167-L168

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

theorem GroundTheory.Global.Cyclotomic.isClosed_ker_degree : IsClosed (degree.ker : Set Gal(ℚ̄/ℚ)) := by sorry
