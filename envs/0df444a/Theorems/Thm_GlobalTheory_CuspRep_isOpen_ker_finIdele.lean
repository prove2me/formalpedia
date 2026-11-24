-- Prove2me | Theorems.Thm_GlobalTheory_CuspRep_isOpen_ker_finIdele
-- name    : GlobalTheory.CuspRep.isOpen_ker_finIdele
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:16.817231+00:00
-- url     : https://prove2.me/theorems/af7cd2a4-2aad-440f-b235-3666c17a85d0
-- title:
--   Cusp Rep: is Open ker fin Idele
-- statement:
--   The Cusp Rep construction uses the is Open ker fin Idele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L32-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L32-L74

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

theorem GlobalTheory.CuspRep.isOpen_ker_finIdele (E : Type) [Field E] [NumberField E] (ψ : (FiniteAdeleRing (𝓞 E) E)ˣ →* ℂˣ)
    (hψ : Continuous ψ) : IsOpen {u | ψ u = 1} := by sorry
