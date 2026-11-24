-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_RootNear_map_sg
-- name    : GlobalTheory.AdLat.RootNear.map_sg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:53:53.744796+00:00
-- url     : https://prove2.me/theorems/e308731a-d856-498a-ab8a-70ef4837626f
-- title:
--   Root Near: map sg
-- statement:
--   The Root Near construction uses the map sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L331-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L331-L338

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
omit [NumberField F] [NumberField E]

theorem GlobalTheory.AdLat.RootNear.map_sg {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (c : E ≃ₐ[F] E)
    (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    Algebra.TensorProduct.map p (AlgHom.id F E) (sg A c z) =
      sg B c (Algebra.TensorProduct.map p (AlgHom.id F E) z) := by sorry
