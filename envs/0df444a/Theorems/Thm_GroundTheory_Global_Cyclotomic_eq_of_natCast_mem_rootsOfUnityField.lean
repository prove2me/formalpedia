-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_eq_of_natCast_mem_rootsOfUnityField
-- name    : GroundTheory.Global.Cyclotomic.eq_of_natCast_mem_rootsOfUnityField
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:14:01.205965+00:00
-- url     : https://prove2.me/theorems/87270cd1-9f56-4dd2-8419-7b463e69b79e
-- title:
--   Cyclotomic: eq of nat Cast mem roots Of Unity Field
-- statement:
--   The Cyclotomic construction uses the eq of nat Cast mem roots Of Unity Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L118-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L118-L143

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

theorem GroundTheory.Global.Cyclotomic.eq_of_natCast_mem_rootsOfUnityField {p : ℕ} [hp : Fact p.Prime] (k : ℕ)
    {Q₁ Q₂ : Ideal (𝓞 (rootsOfUnityField (p ^ (k + 1))))} [Q₁.IsPrime] [Q₂.IsPrime]
    (h₁ : (p : 𝓞 (rootsOfUnityField (p ^ (k + 1)))) ∈ Q₁)
    (h₂ : (p : 𝓞 (rootsOfUnityField (p ^ (k + 1)))) ∈ Q₂) : Q₁ = Q₂ := by sorry
