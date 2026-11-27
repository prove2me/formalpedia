-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_maxCyclotomic_eq_iSup
-- name    : GroundTheory.Global.Cyclotomic.maxCyclotomic_eq_iSup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:17.196337+00:00
-- url     : https://prove2.me/theorems/2bac147a-da3c-42eb-b873-f53853af3e56
-- title:
--   Cyclotomic: max Cyclotomic eq i Sup
-- statement:
--   The Cyclotomic construction uses the max Cyclotomic eq i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L45-L50

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
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
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ

theorem GroundTheory.Global.Cyclotomic.maxCyclotomic_eq_iSup : maxCyclotomic = ⨆ n : ℕ+, rootsOfUnityField n := by sorry
