-- Prove2me | Theorems.Thm_GlobalTheory_CuspRep_unit_ne_zero
-- name    : GlobalTheory.CuspRep.unit_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:47:30.772271+00:00
-- url     : https://prove2.me/theorems/571ccf04-b2e1-40ad-be93-ddfac3be673c
-- title:
--   Cusp Rep: unit ne zero
-- statement:
--   The Cusp Rep construction uses the unit ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L93-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L93-L94

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsOpenKerFinIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CuspRep
variable {ι : Type} [Fintype ι]
omit [Fintype ι]

theorem GlobalTheory.CuspRep.unit_ne_zero (u : (ι → ℂ)ˣ) (i : ι) : (u : ι → ℂ) i ≠ 0 := by sorry
