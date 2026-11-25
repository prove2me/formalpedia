-- Prove2me | Theorems.Thm_GlobalTheory_HyodoDef_PairLin_finrank_add_le
-- name    : GlobalTheory.HyodoDef.PairLin.finrank_add_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:23.449599+00:00
-- url     : https://prove2.me/theorems/aef4e5d9-644a-5b9d-9189-58e0d1f5568b
-- title:
--   Pair Lin: finrank add le
-- statement:
--   The Pair Lin construction uses the finrank add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAnnihilatorAdd.lean#L31-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAnnihilatorAdd.lean#L31-L63

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

theorem GlobalTheory.HyodoDef.PairLin.finrank_add_le (β : M →ₗ[k] M' →ₗ[k] k) (Ag Af : Submodule k M) (Ae Af' : Submodule k M')
    (hN : ∀ b : M', (∀ a : M, β a b = 0) → b ∈ Ae ⊓ Af')
    (hg : ∀ a ∈ Ag, ∀ b ∈ Ae, β a b = 0)
    (hf : ∀ a : M, a ∈ Af ↔ ∀ b ∈ Af', β a b = 0) :
    finrank k Ag + finrank k Ae ≤ finrank k Af + finrank k Af' := by sorry
