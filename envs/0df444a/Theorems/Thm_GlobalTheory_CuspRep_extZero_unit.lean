-- Prove2me | Theorems.Thm_GlobalTheory_CuspRep_extZero_unit
-- name    : GlobalTheory.CuspRep.extZero_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:50.805809+00:00
-- url     : https://prove2.me/theorems/9dbba6d2-c846-4602-adba-06cdb051eebe
-- title:
--   Cusp Rep: ext Zero unit
-- statement:
--   The Cusp Rep construction uses the ext Zero unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L130-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L130-L131

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

theorem GlobalTheory.CuspRep.extZero_unit (ψ : (ι → ℂ)ˣ →* ℂˣ) (u : (ι → ℂ)ˣ) : extZero ψ u = (ψ u : ℂˣ) := by sorry
