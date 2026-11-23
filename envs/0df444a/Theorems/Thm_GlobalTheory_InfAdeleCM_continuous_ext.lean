-- Prove2me | Theorems.Thm_GlobalTheory_InfAdeleCM_continuous_ext
-- name    : GlobalTheory.InfAdeleCM.continuous_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:32.163997+00:00
-- url     : https://prove2.me/theorems/5896a222-59bf-4e6f-8c60-15de416d57dc
-- title:
--   Inf Adele CM: continuous ext
-- statement:
--   The Inf Adele CM construction uses the continuous ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L20-L22

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

theorem GlobalTheory.InfAdeleCM.continuous_ext (σ : F →+* ℂ) : Continuous (ext σ) := by sorry
