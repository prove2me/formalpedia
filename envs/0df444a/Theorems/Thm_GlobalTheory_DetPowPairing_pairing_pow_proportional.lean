-- Prove2me | Theorems.Thm_GlobalTheory_DetPowPairing_pairing_pow_proportional
-- name    : GlobalTheory.DetPowPairing.pairing_pow_proportional
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:42.109519+00:00
-- url     : https://prove2.me/theorems/db751944-460a-400d-be5a-43bcc207e3f4
-- title:
--   Det Pow Pairing: pairing pow proportional
-- statement:
--   The Det Pow Pairing construction uses the pairing pow proportional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FactorialWeightedPairingDetPowProportional.lean#L179-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FactorialWeightedPairingDetPowProportional.lean#L179-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorialWeightedPairingDetPowProportional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPolynomial
open GlobalTheory GlobalTheory.DetPowPairing
variable {C : Type} [CommRing C] {n : ℕ}
open MvPolynomial
variable {C : Type} [CommRing C] {n : ℕ}

theorem GlobalTheory.DetPowPairing.pairing_pow_proportional :
  (∀ (C : Type) [Field C] [CharZero C] (n₀ M Y : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), M ≤ Y → Q.IsHomogeneous (n₀ * M) →
    (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y).support, MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ (Y - M) * Q)) * (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M).support, MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M)) = (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M).support, MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (Q)) * (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y).support, MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y))) := by sorry
