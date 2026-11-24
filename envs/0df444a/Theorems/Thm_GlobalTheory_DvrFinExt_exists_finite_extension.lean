-- Prove2me | Theorems.Thm_GlobalTheory_DvrFinExt_exists_finite_extension
-- name    : GlobalTheory.DvrFinExt.exists_finite_extension
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:52:24.84992+00:00
-- url     : https://prove2.me/theorems/62d81edd-790e-4471-9f92-ab593fc558f7
-- title:
--   Dvr Fin Ext: exists finite extension
-- statement:
--   The Dvr Fin Ext construction uses the exists finite extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtensionCompleteDvrPadicAlgCl.lean#L33-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtensionCompleteDvrPadicAlgCl.lean#L33-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDvrIntegralClosureFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallEqOfIntegralDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtensionCompleteDvrPadicAlgCl
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
open GlobalTheory GlobalTheory.DvrFinExt

theorem GlobalTheory.DvrFinExt.exists_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (maximalIdeal W) W) (_ : CharZero W) (fV : V →+* W) (fK : FractionRing V →+* FractionRing W) (κ' : FractionRing W →+* PadicAlgCl p), Function.Injective fV ∧ IsLocalHom fV ∧ fV.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (fV a)) ∧ κ'.comp fK = κ ∧ (∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ ∀ a, y₀ a ∈ κ'.range := by sorry
