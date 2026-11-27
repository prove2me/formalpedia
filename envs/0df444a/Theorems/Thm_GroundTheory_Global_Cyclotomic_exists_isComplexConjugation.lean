-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_isComplexConjugation
-- name    : GroundTheory.Global.Cyclotomic.exists_isComplexConjugation
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:56:30.206337+00:00
-- url     : https://prove2.me/theorems/44e76e0c-c937-4cf2-9ed3-2c46e7c2dbbb
-- title:
--   Cyclotomic: exists is Complex Conjugation
-- statement:
--   The Cyclotomic construction uses the exists is Complex Conjugation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L128-L131

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

theorem GroundTheory.Global.Cyclotomic.exists_isComplexConjugation : ∃ σ : Gal(ℚ̄/ℚ), IsComplexConjugation σ := by sorry
