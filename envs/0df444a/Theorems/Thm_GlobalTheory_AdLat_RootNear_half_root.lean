-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_RootNear_half_root
-- name    : GlobalTheory.AdLat.RootNear.half_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:16.532199+00:00
-- url     : https://prove2.me/theorems/441ab88c-b9ce-4f88-9e70-9ce0e4ce3a0c
-- title:
--   Root Near: half root
-- statement:
--   The Root Near construction uses the half root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L165-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L165-L173

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
omit [NumberField E]

theorem GlobalTheory.AdLat.RootNear.half_root {A : Type} [CommRing A] [Algebra F A] (c : E ≃ₐ[F] E) (u x : A ⊗[F] E)
    (hu : u * sg A c u = 1) (hx : 2 * x = 1 + u) : x = u * sg A c x := by sorry
