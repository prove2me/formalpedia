-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_genLog_ne_zero
-- name    : GroundTheory.Global.Cyclotomic.genLog_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:13:49.061982+00:00
-- url     : https://prove2.me/theorems/d8eb7778-1fb8-48ee-8b13-427082945246
-- title:
--   Cyclotomic: gen Log ne zero
-- statement:
--   The Cyclotomic construction uses the gen Log ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L189-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L189-L193

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

theorem GroundTheory.Global.Cyclotomic.genLog_ne_zero (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : genLog ℓ ≠ 0 := by sorry
