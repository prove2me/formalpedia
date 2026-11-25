-- Prove2me | Theorems.Thm_GroundTheory_Global_RationalSymbol_unitPart_surjective
-- name    : GroundTheory.Global.RationalSymbol.unitPart_surjective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:19.346635+00:00
-- url     : https://prove2.me/theorems/3261e3ba-95bb-5e9a-8103-3b39b0d53516
-- title:
--   Rational Symbol: unit Part surjective
-- statement:
--   The Rational Symbol construction uses the unit Part surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/RationalCyclotomic.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/RationalCyclotomic.lean#L77-L85

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

theorem GroundTheory.Global.RationalSymbol.unitPart_surjective : Function.Surjective unitPart := by sorry
