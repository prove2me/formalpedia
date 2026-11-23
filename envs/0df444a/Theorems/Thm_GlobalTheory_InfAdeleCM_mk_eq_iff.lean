-- Prove2me | Theorems.Thm_GlobalTheory_InfAdeleCM_mk_eq_iff
-- name    : GlobalTheory.InfAdeleCM.mk_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:51:31.027614+00:00
-- url     : https://prove2.me/theorems/aa1a0230-2e70-460b-b2ec-519ac4de40cf
-- title:
--   Inf Adele CM: mk eq iff
-- statement:
--   The Inf Adele CM construction uses the mk eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L140-L142

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
variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.InfAdeleCM.mk_eq_iff [IsTotallyReal F] {σ σ' : F →+* ℂ} (h : InfinitePlace.mk σ = InfinitePlace.mk σ') : σ = σ' := by sorry
