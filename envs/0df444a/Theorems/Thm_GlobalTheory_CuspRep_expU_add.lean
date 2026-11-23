-- Prove2me | Theorems.Thm_GlobalTheory_CuspRep_expU_add
-- name    : GlobalTheory.CuspRep.expU_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:20.714626+00:00
-- url     : https://prove2.me/theorems/d342558a-cc8a-44d1-a49b-8d3ead4c999d
-- title:
--   Cusp Rep: exp U add
-- statement:
--   The Cusp Rep construction uses the exp U add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L84-L85

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

theorem GlobalTheory.CuspRep.expU_add (z z' : ι → ℂ) : expU (z + z') = expU z * expU z' := by sorry
