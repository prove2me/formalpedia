-- Prove2me | Theorems.Thm_GlobalTheory_CuspRep_expU_log
-- name    : GlobalTheory.CuspRep.expU_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:57.425889+00:00
-- url     : https://prove2.me/theorems/c9d63b72-80f4-45a9-9308-1e63b694aeac
-- title:
--   Cusp Rep: exp U log
-- statement:
--   The Cusp Rep construction uses the exp U log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L98-L99

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

theorem GlobalTheory.CuspRep.expU_log (u : (ι → ℂ)ˣ) : expU (fun i => Complex.log ((u : ι → ℂ) i)) = u := by sorry
