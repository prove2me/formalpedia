-- Prove2me | Theorems.Thm_GlobalTheory_UnimodMass_stabCard_conj
-- name    : GlobalTheory.UnimodMass.stabCard_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:29:46.157212+00:00
-- url     : https://prove2.me/theorems/9761c259-4e89-5977-9202-120eeaea6aa9
-- title:
--   Unimod Mass: stab Card conj
-- statement:
--   The Unimod Mass construction uses the stab Card conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteDcOfCover.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteDcOfCover.lean#L76-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DoubleCosetSetoidRelIffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnimodMass
variable {G : Type*} [Group G]

theorem GlobalTheory.UnimodMass.stabCard_conj (Γ K : Subgroup G) (h g : G) :
    stabCard Γ (K.map (MulAut.conj h).toMonoidHom) g = stabCard Γ K (g * h) := by sorry
