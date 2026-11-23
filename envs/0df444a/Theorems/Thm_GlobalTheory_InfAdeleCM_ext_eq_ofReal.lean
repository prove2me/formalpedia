-- Prove2me | Theorems.Thm_GlobalTheory_InfAdeleCM_ext_eq_ofReal
-- name    : GlobalTheory.InfAdeleCM.ext_eq_ofReal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:13.882505+00:00
-- url     : https://prove2.me/theorems/bf056b86-e3a9-4165-909b-909cf064a657
-- title:
--   Inf Adele CM: ext eq of Real
-- statement:
--   The Inf Adele CM construction uses the ext eq of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L31-L34

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

theorem GlobalTheory.InfAdeleCM.ext_eq_ofReal [IsTotallyReal F] (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = (InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal (InfinitePlace.mk σ)) (a (InfinitePlace.mk σ)) : ℝ) := by sorry
