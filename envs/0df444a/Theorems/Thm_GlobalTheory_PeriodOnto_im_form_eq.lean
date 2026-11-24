-- Prove2me | Theorems.Thm_GlobalTheory_PeriodOnto_im_form_eq
-- name    : GlobalTheory.PeriodOnto.im_form_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:44:19.074994+00:00
-- url     : https://prove2.me/theorems/0af73bef-ebc3-4967-ba23-07d797376aae
-- title:
--   Period Onto: im form eq
-- statement:
--   The Period Onto construction uses the im form eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L207-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L207-L235

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
variable {ι : Type} [Fintype ι] {g r : ℕ} (idx : Fin g ≃ ι × Fin r) (q : ℕ)
variable {Λ : Type} (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
  (e : ι → Λ → Fin r → ℂ) (M : ι → Matrix (Fin r) (Fin r) ℂ)
  (hM : ∀ v t, blockOf idx q t (P v) = M t *ᵥ e t v)
include hspan

theorem GlobalTheory.PeriodOnto.im_form_eq (A : ι → Matrix (Fin r) (Fin r) ℂ) (s : ι → ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ x y, (hermForm Hm (P x) (P y)).im =
      ∑ t, -2 * s t * (blockOf idx q t (P x) ⬝ᵥ A t *ᵥ star (blockOf idx q t (P y))).im)
    (z z' : Fin g → ℂ) : (hermForm Hm z z').im =
      ∑ t, -2 * s t * (blockOf idx q t z ⬝ᵥ A t *ᵥ star (blockOf idx q t z')).im := by sorry
