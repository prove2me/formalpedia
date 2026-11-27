-- Prove2me | Theorems.Thm_GlobalTheory_UnimodMass_finite_dc_of_le
-- name    : GlobalTheory.UnimodMass.finite_dc_of_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:29:56.668935+00:00
-- url     : https://prove2.me/theorems/e057625f-27e8-483a-a0c0-4c1dc3ac124e
-- title:
--   Unimod Mass: finite dc of le
-- statement:
--   The Unimod Mass construction uses the finite dc of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteDcOfCover.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteDcOfCover.lean#L18-L25

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

theorem GlobalTheory.UnimodMass.finite_dc_of_le {Γ W K : Subgroup G} (hWK : W ≤ K) [Finite (DC Γ W)] : Finite (DC Γ K) := by sorry
