-- Prove2me | Theorems.Thm_GlobalTheory_UnimodMass_dcOfCoset_mk
-- name    : GlobalTheory.UnimodMass.dcOfCoset_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:26.552103+00:00
-- url     : https://prove2.me/theorems/25f40455-dc9d-4270-b66a-a41773e7fb2e
-- title:
--   Unimod Mass: dc Of Coset mk
-- statement:
--   The Unimod Mass construction uses the dc Of Coset mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DoubleCosetMassEqRelIndexMulMass.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DoubleCosetMassEqRelIndexMulMass.lean#L23-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DoubleCosetMassEqRelIndexMulMass
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

theorem GlobalTheory.UnimodMass.dcOfCoset_mk (Γ W K : Subgroup G) (t : G) (k : K) :
    dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) = Quotient.mk (dcSetoid Γ W) (t * k) := by sorry
