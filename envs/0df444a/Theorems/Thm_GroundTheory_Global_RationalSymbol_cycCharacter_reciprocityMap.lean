-- Prove2me | Theorems.Thm_GroundTheory_Global_RationalSymbol_cycCharacter_reciprocityMap
-- name    : GroundTheory.Global.RationalSymbol.cycCharacter_reciprocityMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:59:06.528515+00:00
-- url     : https://prove2.me/theorems/123b1cec-e9f8-411b-a6f4-919fc3a18307
-- title:
--   Rational Symbol: cyc Character reciprocity Map
-- statement:
--   The Rational Symbol construction uses the cyc Character reciprocity Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/RationalCyclotomic.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/RationalCyclotomic.lean#L97-L99

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

theorem GroundTheory.Global.RationalSymbol.cycCharacter_reciprocityMap (x : IdeleClassGroup ℚ) :
    cycCharacter (reciprocityMap x) = (unitPart x)⁻¹ := by sorry
