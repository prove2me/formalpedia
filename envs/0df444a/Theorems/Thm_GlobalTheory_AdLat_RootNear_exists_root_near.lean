-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_RootNear_exists_root_near
-- name    : GlobalTheory.AdLat.RootNear.exists_root_near
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:54:15.883173+00:00
-- url     : https://prove2.me/theorems/c3cb696e-3b56-4eac-90da-ee7db00f520d
-- title:
--   Root Near: exists root near
-- statement:
--   The Root Near construction uses the exists root near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L340-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L340-L388

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear
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
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.AdLat.RootNear.exists_root_near : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); ∀ W ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), ∃ N ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), ∀ u ∈ N, (u : AdeleRing (𝓞 F) F ⊗[F] E) * sg (AdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ W, (x : AdeleRing (𝓞 F) F ⊗[F] E) = u * sg (AdeleRing (𝓞 F) F) c x := by sorry
