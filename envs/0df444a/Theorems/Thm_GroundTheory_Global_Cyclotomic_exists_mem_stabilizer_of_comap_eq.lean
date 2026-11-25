-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_stabilizer_of_comap_eq
-- name    : GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_of_comap_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:44:10.176742+00:00
-- url     : https://prove2.me/theorems/2ed72ba8-f4d3-40d2-9e6e-702ca3201634
-- title:
--   Cyclotomic: exists mem stabilizer of comap eq
-- statement:
--   The Cyclotomic construction uses the exists mem stabilizer of comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L34-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L34-L68

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

theorem GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_of_comap_eq (L : IntermediateField ℚ ℚ̄) (P : Ideal (𝓞 ℚ̄))
    [P.IsPrime] (τ : Gal(ℚ̄/ℚ))
    (h : (τ⁻¹ • P).comap (ringOfIntegersIncl L) = P.comap (ringOfIntegersIncl L)) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, ∀ x ∈ L, σ x = τ x := by sorry
