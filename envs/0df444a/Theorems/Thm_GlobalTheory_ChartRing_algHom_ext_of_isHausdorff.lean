-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_algHom_ext_of_isHausdorff
-- name    : GlobalTheory.ChartRing.algHom_ext_of_isHausdorff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:15.823622+00:00
-- url     : https://prove2.me/theorems/78280594-7934-49df-8f53-5a578f42cd4f
-- title:
--   Chart Ring: alg Hom ext of is Hausdorff
-- statement:
--   The Chart Ring construction uses the alg Hom ext of is Hausdorff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L98-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L98-L108

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
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable (J : Ideal S) [IsAdicComplete J S] {s : S} (hs : s ∈ J)

theorem GlobalTheory.ChartRing.algHom_ext_of_isHausdorff (J : Ideal S) [IsHausdorff J S] {φ ψ : A⟦X⟧ →ₐ[A] S}
    (hφ : φ X ∈ J) (h : φ X = ψ X) : φ = ψ := by sorry
