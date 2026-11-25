-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finite_extension_complete_dvr_padicAlgCl
-- name    : GlobalTheory.T.exists_finite_extension_complete_dvr_padicAlgCl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:55.375796+00:00
-- url     : https://prove2.me/theorems/b3e50100-7cb5-4904-a0b7-41de236ae97d
-- title:
--   T: exists finite extension complete dvr padic Alg Cl
-- statement:
--   The T construction uses the exists finite extension complete dvr padic Alg Cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtensionCompleteDvrPadicAlgClStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtensionCompleteDvrPadicAlgClStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtensionCompleteDvrPadicAlgCl
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDvrIntegralClosureFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallEqOfIntegralDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtensionCompleteDvrPadicAlgClStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finite_extension_complete_dvr_padicAlgCl : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (maximalIdeal W) W) (_ : CharZero W) (fV : V →+* W) (fK : FractionRing V →+* FractionRing W) (κ' : FractionRing W →+* PadicAlgCl p), Function.Injective fV ∧ IsLocalHom fV ∧ fV.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (fV a)) ∧ κ'.comp fK = κ ∧ (∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ ∀ a, y₀ a ∈ κ'.range := by sorry
