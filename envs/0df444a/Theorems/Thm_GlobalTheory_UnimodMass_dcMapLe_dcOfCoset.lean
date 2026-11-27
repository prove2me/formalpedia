-- Prove2me | Theorems.Thm_GlobalTheory_UnimodMass_dcMapLe_dcOfCoset
-- name    : GlobalTheory.UnimodMass.dcMapLe_dcOfCoset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:26.404546+00:00
-- url     : https://prove2.me/theorems/4da53b24-ff4d-468e-9fd4-c4271e0913b5
-- title:
--   Unimod Mass: dc Map Le dc Of Coset
-- statement:
--   The Unimod Mass construction uses the dc Map Le dc Of Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DoubleCosetMassEqRelIndexMulMass.lean#L123-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DoubleCosetMassEqRelIndexMulMass.lean#L123-L129

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
open scoped BigOperators

theorem GlobalTheory.UnimodMass.dcMapLe_dcOfCoset {G : Type} [Group G] {Γ W K : Subgroup G} (hWK : W ≤ K) (t : G)
    (x : K ⧸ W.subgroupOf K) : dcMapLe hWK (dcOfCoset Γ W K t x) = Quotient.mk (dcSetoid Γ K) t := by sorry
