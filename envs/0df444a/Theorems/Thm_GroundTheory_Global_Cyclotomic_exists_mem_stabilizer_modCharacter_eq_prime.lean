-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_stabilizer_modCharacter_eq_prime
-- name    : GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_modCharacter_eq_prime
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:12:46.528092+00:00
-- url     : https://prove2.me/theorems/6f713f10-6e88-4f31-bc90-12486a2612b4
-- title:
--   Cyclotomic: exists mem stabilizer mod Character eq prime
-- statement:
--   The Cyclotomic construction uses the exists mem stabilizer mod Character eq prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L87-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L87-L116

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

theorem GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_modCharacter_eq_prime {p : ℕ} [Fact p.Prime] (P : Ideal (𝓞 ℚ̄))
    [P.IsPrime] [hP : P.LiesOver (Ideal.span {(p : ℤ)})] {M : ℕ} [NeZero M] (hM : ¬ p ∣ M) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, (modCharacter M σ : ZMod M) = p := by sorry
