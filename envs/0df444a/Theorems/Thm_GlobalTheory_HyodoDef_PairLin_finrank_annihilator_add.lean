-- Prove2me | Theorems.Thm_GlobalTheory_HyodoDef_PairLin_finrank_annihilator_add
-- name    : GlobalTheory.HyodoDef.PairLin.finrank_annihilator_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:37:46.173844+00:00
-- url     : https://prove2.me/theorems/d65c938c-a979-4f27-9784-93484e005882
-- title:
--   Pair Lin: finrank annihilator add
-- statement:
--   The Pair Lin construction uses the finrank annihilator add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAnnihilatorAdd.lean#L10-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAnnihilatorAdd.lean#L10-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAnnihilatorAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.HyodoDef GlobalTheory.HyodoDef.PairLin
variable {k M M' : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [FiniteDimensional k M] [FiniteDimensional k M']

theorem GlobalTheory.HyodoDef.PairLin.finrank_annihilator_add (β : M →ₗ[k] M' →ₗ[k] k) (S : Submodule k M')
    (hS : LinearMap.ker β.flip ≤ S) :
    finrank k (LinearMap.ker (S.subtype.dualMap ∘ₗ β)) + finrank k S
      = finrank k M + finrank k (LinearMap.ker β.flip) := by sorry
