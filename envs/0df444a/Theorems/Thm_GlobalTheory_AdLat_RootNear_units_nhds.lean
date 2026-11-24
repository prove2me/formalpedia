-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_RootNear_units_nhds
-- name    : GlobalTheory.AdLat.RootNear.units_nhds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:53:48.438518+00:00
-- url     : https://prove2.me/theorems/0ff93feb-1a28-4617-83cd-636cfd07c825
-- title:
--   Root Near: units nhds
-- statement:
--   The Root Near construction uses the units nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L321-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L321-L328

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

theorem GlobalTheory.AdLat.RootNear.units_nhds {M : Type} [Monoid M] [TopologicalSpace M] (W : Set Mˣ) (hW : W ∈ 𝓝 (1 : Mˣ)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ x : Mˣ, (x : M) ∈ V → ((x⁻¹ : Mˣ) : M) ∈ V → x ∈ W := by sorry
