-- Prove2me | Theorems.Thm_GlobalTheory_realLinear_injective_of_countable_ker
-- name    : GlobalTheory.realLinear_injective_of_countable_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:43.493873+00:00
-- url     : https://prove2.me/theorems/2db39259-6035-4621-94a9-b8ce338eb5e3
-- title:
--   Global Theory: real Linear injective of countable ker
-- statement:
--   The Global Theory construction uses the real Linear injective of countable ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L79-L83

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
variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]

theorem GlobalTheory.realLinear_injective_of_countable_ker (L : M →ₗ[ℝ] N) (h : {x | L x = 0}.Countable) :
    Function.Injective L := by sorry
