-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayData_cnt_of_ne_zero
-- name    : GlobalTheory.Mem.RayData.cnt_of_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:50.777379+00:00
-- url     : https://prove2.me/theorems/5054ef05-1e70-4c0a-8c47-38e1c3e83b81
-- title:
--   Ray Data: cnt of ne zero
-- statement:
--   The Ray Data construction uses the cnt of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L289-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L289-L295

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem
open NumberField IsDedekindDomain
attribute [instance] RayData.grp RayData.fin
open GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)

theorem GlobalTheory.Mem.RayData.cnt_of_ne_zero (c : D.G) {n : ℕ} (hn : n ≠ 0) : D.cnt c n =
    (Nat.card {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ I ≠ ⊥ ∧ Ideal.absNorm I = n ∧ D.cls I = c} : ℕ) := by sorry
