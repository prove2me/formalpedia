-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_map_comap_constantCoeff_le
-- name    : GlobalTheory.ChartRing.map_comap_constantCoeff_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:20.110805+00:00
-- url     : https://prove2.me/theorems/0395c335-b7c3-4a3a-8ac0-dbd70bfa5afd
-- title:
--   Chart Ring: map comap constant Coeff le
-- statement:
--   The Chart Ring construction uses the map comap constant Coeff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L241-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L241-L250

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A : Type*} [CommRing A] (I : Ideal A)

theorem GlobalTheory.ChartRing.map_comap_constantCoeff_le {S : Type*} [CommRing S] [Algebra A S] (J : Ideal S)
    (φ : A⟦X⟧ →ₐ[A] S) (hI : I.map (algebraMap A S) ≤ J) (hX : φ X ∈ J) :
    (I.comap (constantCoeff (R := A))).map φ ≤ J := by sorry
