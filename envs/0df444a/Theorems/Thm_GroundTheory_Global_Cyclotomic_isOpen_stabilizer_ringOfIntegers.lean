-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_isOpen_stabilizer_ringOfIntegers
-- name    : GroundTheory.Global.Cyclotomic.isOpen_stabilizer_ringOfIntegers
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:44:08.725798+00:00
-- url     : https://prove2.me/theorems/b1fb49ba-f4f9-4e5a-ae56-841d496599ec
-- title:
--   Cyclotomic: is Open stabilizer ring Of Integers
-- statement:
--   The Cyclotomic construction uses the is Open stabilizer ring Of Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L18-L25

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

theorem GroundTheory.Global.Cyclotomic.isOpen_stabilizer_ringOfIntegers (b : 𝓞 ℚ̄) :
    IsOpen (MulAction.stabilizer Gal(ℚ̄/ℚ) b : Set Gal(ℚ̄/ℚ)) := by sorry
