-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_isClosed_stabilizer
-- name    : GroundTheory.Global.Cyclotomic.isClosed_stabilizer
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:08.377356+00:00
-- url     : https://prove2.me/theorems/021a5364-bad0-4c09-b26a-60dd7f3cc27e
-- title:
--   Cyclotomic: is Closed stabilizer
-- statement:
--   The Cyclotomic construction uses the is Closed stabilizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L231-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L231-L262

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

theorem GroundTheory.Global.Cyclotomic.isClosed_stabilizer (P : Ideal (𝓞 ℚ̄)) :
    IsClosed (MulAction.stabilizer Gal(ℚ̄/ℚ) P : Set Gal(ℚ̄/ℚ)) := by sorry
