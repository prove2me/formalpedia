-- Prove2me | Theorems.Thm_GlobalTheory_tau_basis_unit_determinant_exists_basis_isUnit_det
-- name    : GlobalTheory.tau_basis_unit_determinant.exists_basis_isUnit_det
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:49.456033+00:00
-- url     : https://prove2.me/theorems/b3a56efe-7adc-4c05-a9b6-8efbe85d62cf
-- title:
--   tau basis unit determinant: exists basis is Unit det
-- statement:
--   The tau basis unit determinant construction uses the exists basis is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TauBasisUnitDeterminant.lean#L9-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TauBasisUnitDeterminant.lean#L9-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitDeterminantBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TauBasisUnitDeterminant
import Theorems.Thm_GlobalTheory_UnitDeterminantBasis_exists_basis_isUnit_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory GlobalTheory.tau_basis_unit_determinant

theorem GlobalTheory.tau_basis_unit_determinant.exists_basis_isUnit_det : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Free ℤ OE] [Module.Finite ℤ OE] (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[p] O] (w : PlaceU p OE) (t : Fin w.n → (OE →+* O)),
    (∀ j, t j ∈ Emb (O := O) w.e) →
    (∀ j j', (∀ x, t j x - t j' x ∈ maximalIdeal O) → j = j') →
    ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j => tauExt (t j) (b i : ℤ_[p] ⊗[ℤ] OE))) := by sorry
