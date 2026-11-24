-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_integral_unit_root_norm_one_adele
-- name    : GlobalTheory.T.exists_integral_unit_root_norm_one_adele
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:50.466364+00:00
-- url     : https://prove2.me/theorems/1435c50e-70a0-41b8-9eb2-304268d389fd
-- title:
--   T: exists integral unit root norm one adele
-- statement:
--   The T construction uses the exists integral unit root norm one adele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdeleStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdeleStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_integral_unit_root_norm_one_adele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → ∀ u ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), (∃ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), x * y = 1) ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x := by sorry
