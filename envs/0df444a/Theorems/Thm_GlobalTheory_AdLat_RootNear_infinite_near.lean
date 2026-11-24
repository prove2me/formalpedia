-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_RootNear_infinite_near
-- name    : GlobalTheory.AdLat.RootNear.infinite_near
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:54:19.470711+00:00
-- url     : https://prove2.me/theorems/f667ad2b-2913-4a27-a49a-102210f9c475
-- title:
--   Root Near: infinite near
-- statement:
--   The Root Near construction uses the infinite near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L281-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L281-L319

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

theorem GlobalTheory.AdLat.RootNear.infinite_near (c : E ≃ₐ[F] E) :
    letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
      moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
    ∀ V ∈ 𝓝 (1 : InfiniteAdeleRing F ⊗[F] E), ∀ᶠ u in 𝓝 (1 : InfiniteAdeleRing F ⊗[F] E),
      u * sg (InfiniteAdeleRing F) c u = 1 →
      ∃ x ∈ V, ∃ y ∈ V, x * y = 1 ∧ x = u * sg (InfiniteAdeleRing F) c x := by sorry
