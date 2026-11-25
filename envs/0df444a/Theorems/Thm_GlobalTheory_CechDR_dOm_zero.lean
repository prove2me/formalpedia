-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_dOm_zero
-- name    : GlobalTheory.CechDR.dOm_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:25.594804+00:00
-- url     : https://prove2.me/theorems/094dcd40-17de-4b21-8385-3ec81081fe6a
-- title:
--   Cech DR: d Om zero
-- statement:
--   The Cech DR construction uses the d Om zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L300-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L300-L301

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
variable {R B}

theorem GlobalTheory.CechDR.dOm_zero (b : B) (h : algebraMap B (DR R B) b ∈ ⋀[B]^0 Ω[B⁄R]) :
    dOm R B 0 ⟨_, h⟩ = ⟨ι1 (D R B b), ι_mem _⟩ := by sorry
