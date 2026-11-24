-- Prove2me | Theorems.Thm_GlobalTheory_IntegralMultiple_coe_smul_mem
-- name    : GlobalTheory.IntegralMultiple.coe_smul_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:20:38.390163+00:00
-- url     : https://prove2.me/theorems/edad0af2-6da8-481a-995f-e0d6e026fbb9
-- title:
--   Integral Multiple: coe smul mem
-- statement:
--   The Integral Multiple construction uses the coe smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CoeSmulMem.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CoeSmulMem.lean#L15-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoeSmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultiple
open NumberField

theorem GlobalTheory.IntegralMultiple.coe_smul_mem {E : Type} [Field E] [NumberField E] {j : ℕ}
    (Λ : Submodule (𝓞 E) (Fin j → E)) (r : 𝓞 E) {v : Fin j → E} (hv : v ∈ Λ) :
    (r : E) • v ∈ Λ := by sorry
