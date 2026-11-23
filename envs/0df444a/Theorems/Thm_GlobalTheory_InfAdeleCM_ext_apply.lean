-- Prove2me | Theorems.Thm_GlobalTheory_InfAdeleCM_ext_apply
-- name    : GlobalTheory.InfAdeleCM.ext_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:30.45596+00:00
-- url     : https://prove2.me/theorems/7c810349-381a-4b76-9a5e-26c20e1ae772
-- title:
--   Inf Adele CM: ext apply
-- statement:
--   The Inf Adele CM construction uses the ext apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L17-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.InfAdeleCM
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.InfAdeleCM.ext_apply (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ) (a (InfinitePlace.mk σ)) := by sorry
