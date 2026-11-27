-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_coe_ringOfIntegersIncl
-- name    : GroundTheory.Global.Cyclotomic.coe_ringOfIntegersIncl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:55:55.090434+00:00
-- url     : https://prove2.me/theorems/c0fa6ffa-1175-4302-8676-30a31c52ad7a
-- title:
--   Cyclotomic: coe ring Of Integers Incl
-- statement:
--   The Cyclotomic construction uses the coe ring Of Integers Incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L30-L32

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ

theorem GroundTheory.Global.Cyclotomic.coe_ringOfIntegersIncl (L : IntermediateField ℚ ℚ̄) (a : 𝓞 L) :
    ((ringOfIntegersIncl L a : 𝓞 ℚ̄) : ℚ̄) = ((a : L) : ℚ̄) := by sorry
