-- Prove2me | Theorems.Thm_GlobalTheory_CuspRep_extZero_eventually
-- name    : GlobalTheory.CuspRep.extZero_eventually
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:36.762156+00:00
-- url     : https://prove2.me/theorems/d301e7cd-a3dd-472e-81f3-0030582293eb
-- title:
--   Cusp Rep: ext Zero eventually
-- statement:
--   The Cusp Rep construction uses the ext Zero eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L133-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsOpenKerFinIdele.lean#L133-L143

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

theorem GlobalTheory.CuspRep.extZero_eventually {ψ : (ι → ℂ)ˣ →* ℂˣ} {L : (ι → ℂ) →L[ℝ] ℂ}
    (hL : ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z)) (u : (ι → ℂ)ˣ) :
    extZero ψ =ᶠ[𝓝 (u : ι → ℂ)] fun x => (ψ u : ℂˣ) * Complex.exp (L fun i => Complex.log (x i / (u : ι → ℂ) i)) := by sorry
