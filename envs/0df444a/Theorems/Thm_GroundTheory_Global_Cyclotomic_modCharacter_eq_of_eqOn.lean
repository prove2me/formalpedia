-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_modCharacter_eq_of_eqOn
-- name    : GroundTheory.Global.Cyclotomic.modCharacter_eq_of_eqOn
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:43.9218+00:00
-- url     : https://prove2.me/theorems/a4b1389f-41fd-45fb-b604-57945b45b99b
-- title:
--   Cyclotomic: mod Character eq of eq On
-- statement:
--   The Cyclotomic construction uses the mod Character eq of eq On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L74-L77

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

theorem GroundTheory.Global.Cyclotomic.modCharacter_eq_of_eqOn {M : ℕ} [NeZero M] {σ τ : Gal(ℚ̄/ℚ)}
    (h : ∀ x ∈ rootsOfUnityField M, σ x = τ x) : modCharacter M σ = modCharacter M τ := by sorry
