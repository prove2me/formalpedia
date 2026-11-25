-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_infinite_decompositionComponentImage
-- name    : GroundTheory.Global.Cyclotomic.infinite_decompositionComponentImage
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:55:26.183408+00:00
-- url     : https://prove2.me/theorems/2a62cce7-a90b-42b6-9b3a-116cb6fb33a2
-- title:
--   Cyclotomic: infinite decomposition Component Image
-- statement:
--   The Cyclotomic construction uses the infinite decomposition Component Image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L326-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L326-L330

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
variable (q : Nat.Primes) (P : Ideal (𝓞 ℚ̄))

theorem GroundTheory.Global.Cyclotomic.infinite_decompositionComponentImage (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (decompositionComponentImage q P : Set ℤ_[q]).Infinite := by sorry
