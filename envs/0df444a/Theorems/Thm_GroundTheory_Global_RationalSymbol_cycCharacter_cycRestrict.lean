-- Prove2me | Theorems.Thm_GroundTheory_Global_RationalSymbol_cycCharacter_cycRestrict
-- name    : GroundTheory.Global.RationalSymbol.cycCharacter_cycRestrict
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:17.077908+00:00
-- url     : https://prove2.me/theorems/1378f0d9-d489-520f-94fb-7fba6dff6c62
-- title:
--   Rational Symbol: cyc Character cyc Restrict
-- statement:
--   The Rational Symbol construction uses the cyc Character cyc Restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/RationalCyclotomic.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/RationalCyclotomic.lean#L56-L62

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

theorem GroundTheory.Global.RationalSymbol.cycCharacter_cycRestrict (σ : Gal(ℚ̄/ℚ)) : cycCharacter (cycRestrict σ) = character σ := by sorry
