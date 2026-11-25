-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_stabilizer_modCharacter_eq_of_prime_pow
-- name    : GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_modCharacter_eq_of_prime_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:20:44.314319+00:00
-- url     : https://prove2.me/theorems/086a3bf6-76e9-4737-9075-948ca31d1b14
-- title:
--   Cyclotomic: exists mem stabilizer mod Character eq of prime pow
-- statement:
--   The Cyclotomic construction uses the exists mem stabilizer mod Character eq of prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L145-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L145-L166

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

theorem GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_modCharacter_eq_of_prime_pow {p : ℕ} [hp : Fact p.Prime]
    (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] [hP : P.LiesOver (Ideal.span {(p : ℤ)})] (k : ℕ)
    (a : (ZMod (p ^ (k + 1)))ˣ) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, modCharacter (p ^ (k + 1)) σ = a := by sorry
