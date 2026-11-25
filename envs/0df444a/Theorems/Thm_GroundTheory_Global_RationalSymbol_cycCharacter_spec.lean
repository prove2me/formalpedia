-- Prove2me | Theorems.Thm_GroundTheory_Global_RationalSymbol_cycCharacter_spec
-- name    : GroundTheory.Global.RationalSymbol.cycCharacter_spec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:55:47.30302+00:00
-- url     : https://prove2.me/theorems/e2dce6db-1d26-5c65-b9ec-92a32f3c9dc6
-- title:
--   Rational Symbol: cyc Character spec
-- statement:
--   The Rational Symbol construction uses the cyc Character spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/RationalCyclotomic.lean#L64-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/RationalCyclotomic.lean#L64-L71

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

theorem GroundTheory.Global.RationalSymbol.cycCharacter_spec (τ : Gal(maxCyclotomic/ℚ)) (n : ℕ+) {ζ : maxCyclotomic}
    (hζ : ζ ^ (n : ℕ) = 1) :
    τ ζ = ζ ^ (ProfiniteInteger.proj n (cycCharacter τ : ℤ̂)).val := by sorry
