-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_decompositionComponentImage_ne_zero
-- name    : GroundTheory.Global.Cyclotomic.exists_mem_decompositionComponentImage_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:27.376457+00:00
-- url     : https://prove2.me/theorems/2846aa5e-af37-4187-b0ce-342675aafbdb
-- title:
--   Cyclotomic: exists mem decomposition Component Image ne zero
-- statement:
--   The Cyclotomic construction uses the exists mem decomposition Component Image ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L312-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L312-L318

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

theorem GroundTheory.Global.Cyclotomic.exists_mem_decompositionComponentImage_ne_zero (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ x ∈ decompositionComponentImage q P, x ≠ 0 := by sorry
