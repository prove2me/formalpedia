-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_exists_integral_unit_root
-- name    : GlobalTheory.AdLat.exists_integral_unit_root
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:26.300478+00:00
-- url     : https://prove2.me/theorems/9189770f-a35a-4dcc-aa13-6aace1a66f20
-- title:
--   Ad Lat: exists integral unit root
-- statement:
--   The Ad Lat construction uses the exists integral unit root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L364-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L364-L541

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
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
open GlobalTheory GlobalTheory.AdLat
open UnitRoot
open NumberField IsDedekindDomain
open scoped TensorProduct Topology Matrix

theorem GlobalTheory.AdLat.exists_integral_unit_root : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → ∀ u ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), u * _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), (∃ y ∈ _root_.GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), x * y = 1) ∧ x = u * _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c x := by sorry
