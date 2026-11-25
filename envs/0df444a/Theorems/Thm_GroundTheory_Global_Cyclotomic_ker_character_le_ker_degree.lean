-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_ker_character_le_ker_degree
-- name    : GroundTheory.Global.Cyclotomic.ker_character_le_ker_degree
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:19:16.254237+00:00
-- url     : https://prove2.me/theorems/7d7c17c3-7cf0-4d4a-aa03-f511c979efb5
-- title:
--   Cyclotomic: ker character le ker degree
-- statement:
--   The Cyclotomic construction uses the ker character le ker degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L92-L93

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

theorem GroundTheory.Global.Cyclotomic.ker_character_le_ker_degree : character.ker ≤ degree.ker := by sorry
