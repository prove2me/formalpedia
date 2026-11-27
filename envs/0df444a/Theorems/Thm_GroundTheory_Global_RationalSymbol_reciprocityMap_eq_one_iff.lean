-- Prove2me | Theorems.Thm_GroundTheory_Global_RationalSymbol_reciprocityMap_eq_one_iff
-- name    : GroundTheory.Global.RationalSymbol.reciprocityMap_eq_one_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:55.580109+00:00
-- url     : https://prove2.me/theorems/b29e5356-f0b8-5d43-920c-b424c6ac4e8c
-- title:
--   Rational Symbol: reciprocity Map eq one iff
-- statement:
--   The Rational Symbol construction uses the reciprocity Map eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/RationalCyclotomic.lean#L107-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/RationalCyclotomic.lean#L107-L115

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Rational
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_RationalCyclotomic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField IdeleGroup IntermediateField
open scoped GroundTheory.LocalField.Abstract
noncomputable section
open GroundTheory.Global.RationalSymbol
open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ

theorem GroundTheory.Global.RationalSymbol.reciprocityMap_eq_one_iff (x : IdeleClassGroup ℚ) :
    reciprocityMap x = 1 ↔ (RationalIdeles.ideleClassGroupEquiv x).2 = 1 := by sorry
