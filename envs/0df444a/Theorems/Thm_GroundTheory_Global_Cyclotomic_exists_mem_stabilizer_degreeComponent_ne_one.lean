-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_stabilizer_degreeComponent_ne_one
-- name    : GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_degreeComponent_ne_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:00.413801+00:00
-- url     : https://prove2.me/theorems/c05a3ac6-1131-441d-892a-ad3f42029995
-- title:
--   Cyclotomic: exists mem stabilizer degree Component ne one
-- statement:
--   The Cyclotomic construction uses the exists mem stabilizer degree Component ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L195-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L195-L225

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

theorem GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_degreeComponent_ne_one {p : ℕ} [hp : Fact p.Prime]
    (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (q : Nat.Primes) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, degreeComponent q σ ≠ 1 := by sorry
