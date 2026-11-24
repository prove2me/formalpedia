-- Prove2me | Theorems.Thm_GlobalTheory_PeriodOnto_exists_frames
-- name    : GlobalTheory.PeriodOnto.exists_frames
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:57.535314+00:00
-- url     : https://prove2.me/theorems/93f8135b-6533-46ff-8242-5b55f412b134
-- title:
--   Period Onto: exists frames
-- statement:
--   The Period Onto construction uses the exists frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L309-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L309-L355

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

theorem GlobalTheory.PeriodOnto.exists_frames {ι : Type} [Fintype ι] {g r : ℕ} (idx : Fin g ≃ ι × Fin r) (q : ℕ) {Λ : Type}
    (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (e : ι → Λ → Fin r → ℂ) (M : ι → Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ v t, blockOf idx q t (P v) = M t *ᵥ e t v) (G : ι → Matrix (Fin r) (Fin r) ℂ)
    (hGH : ∀ t, (G t).IsHermitian) (s : ι → ℝ) (hs : ∀ t, 0 < s t) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (h : ∀ x y, (hermForm Hm (P x) (P y)).im = ∑ t, -2 * s t * (e t x ⬝ᵥ G t *ᵥ star (e t y)).im)
    (t : ι) :
    ∃ x : Matrix (Fin r) (Fin r) ℂ, x.det ≠ 0 ∧ (sgnMat r q * (xᵀ * G t * x.map conj)).PosDef ∧
      ∀ (v : Λ) (a : Fin r), P v (idx.symm (t, a)) =
        if (a : ℕ) < q then conj ((e t v ᵥ* (G t * x.map conj)) a) else (x⁻¹ *ᵥ e t v) a := by sorry
