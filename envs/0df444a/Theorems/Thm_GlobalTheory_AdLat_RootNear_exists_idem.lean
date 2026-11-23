-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_RootNear_exists_idem
-- name    : GlobalTheory.AdLat.RootNear.exists_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:02.602807+00:00
-- url     : https://prove2.me/theorems/275f33e3-ea95-4bd0-b09e-fb867f28fa28
-- title:
--   Root Near: exists idem
-- statement:
--   The Root Near construction uses the exists idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L71-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsRootNear.lean#L71-L88

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

theorem GlobalTheory.AdLat.RootNear.exists_idem {ι : Type} (O : ι → Type) [∀ v, CommRing (O v)] [∀ v, IsLocalRing (O v)] (n : ℕ) :
    ∃ e f : ∀ v, O v, e * e = e ∧ 1 - e = n * f ∧ ∀ a, IsUnit (1 + e * n * a) := by sorry
