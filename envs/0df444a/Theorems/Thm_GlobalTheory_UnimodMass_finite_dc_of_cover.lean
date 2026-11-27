-- Prove2me | Theorems.Thm_GlobalTheory_UnimodMass_finite_dc_of_cover
-- name    : GlobalTheory.UnimodMass.finite_dc_of_cover
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:29:59.991057+00:00
-- url     : https://prove2.me/theorems/56acf112-9f3a-5fc3-8b1c-9ac0d209fa9f
-- title:
--   Unimod Mass: finite dc of cover
-- statement:
--   The Unimod Mass construction uses the finite dc of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteDcOfCover.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteDcOfCover.lean#L27-L33

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

theorem GlobalTheory.UnimodMass.finite_dc_of_cover {Γ K : Subgroup G} (hT : ∃ T : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ t ∈ T, ∃ κ ∈ K, g = γ * t * κ) :
    Finite (DC Γ K) := by sorry
