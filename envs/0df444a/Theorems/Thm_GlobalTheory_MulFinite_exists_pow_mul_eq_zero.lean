-- Prove2me | Theorems.Thm_GlobalTheory_MulFinite_exists_pow_mul_eq_zero
-- name    : GlobalTheory.MulFinite.exists_pow_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:28:13.213366+00:00
-- url     : https://prove2.me/theorems/497e3ee0-9cd8-4f03-8c0b-391bf3cf058a
-- title:
--   Mul Finite: exists pow mul eq zero
-- statement:
--   The Mul Finite construction uses the exists pow mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomFromSpecResidueField.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomFromSpecResidueField.lean#L15-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.MulFinite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial

theorem GlobalTheory.MulFinite.exists_pow_mul_eq_zero {k R : Type} [CommRing k] [CommRing R] (hk : IsField k) (φ : k →+* R)
    (a : R) (ha : φ.IsIntegralElem a) :
    ∃ (m : ℕ) (c b : R), IsUnit c ∧ a ^ m * (c + a * b) = 0 := by sorry
