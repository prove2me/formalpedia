-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_realLinear_of_eventually_add_mod_discrete
-- name    : GlobalTheory.existsUnique_realLinear_of_eventually_add_mod_discrete
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:25.847802+00:00
-- url     : https://prove2.me/theorems/732b11c4-9ad5-4f8a-9ac8-106bc2b9c3f0
-- title:
--   Global Theory: exists Unique real Linear of eventually add mod discrete
-- statement:
--   The Global Theory construction uses the exists Unique real Linear of eventually add mod discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L22-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L22-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem GlobalTheory.existsUnique_realLinear_of_eventually_add_mod_discrete {Γ : AddSubgroup F}
    (hΓ : IsDiscrete (Γ : Set F)) {g : E → F} (hc : ContinuousAt g 0) (h0 : g 0 = 0)
    (hg : ∀ᶠ p : E × E in 𝓝 0, g (p.1 + p.2) - g p.1 - g p.2 ∈ Γ) :
    ∃! L : E →L[ℝ] F, g =ᶠ[𝓝 0] L := by sorry
