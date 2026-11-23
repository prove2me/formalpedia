-- Prove2me | Theorems.Thm_GlobalTheory_InfAdeleCM_ext_algebraMap
-- name    : GlobalTheory.InfAdeleCM.ext_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:29.694561+00:00
-- url     : https://prove2.me/theorems/ed654e9a-2226-45a0-93cc-d13f72fcc26c
-- title:
--   Inf Adele CM: ext algebra Map
-- statement:
--   The Inf Adele CM construction uses the ext algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean#L24-L29

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

theorem GlobalTheory.InfAdeleCM.ext_algebraMap [IsTotallyReal F] (σ : F →+* ℂ) (x : F) :
    ext σ (algebraMap F (InfiniteAdeleRing F) x) = σ x := by sorry
