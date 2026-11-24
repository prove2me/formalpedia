-- Prove2me | Theorems.Thm_GlobalTheory_FramePeriod_block_of_allPer
-- name    : GlobalTheory.FramePeriod.block_of_allPer
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:58:04.936288+00:00
-- url     : https://prove2.me/theorems/26b9b2df-f72d-47ec-9b94-cb74da269412
-- title:
--   Frame Period: block of all Per
-- statement:
--   The Frame Period construction uses the block of all Per property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FrameOfPeriodLinear.lean#L79-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FrameOfPeriodLinear.lean#L79-L115

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.FramePeriod.block_of_allPer {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ)
    (x x' : FD.Frame Ψ r) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (h : Matrix (Fin g) (Fin g) ℂ)
    (hs : Function.Surjective (allPer Gm q x idx))
    (hh : ∀ y, allPer Gm q x' idx y = h *ᵥ allPer Gm q x idx y) (k k' : Fin g)
    (hk : ¬ ((idx k).1 = (idx k').1 ∧ (((idx k).2 : ℕ) < q ↔ ((idx k').2 : ℕ) < q))) : h k k' = 0 := by sorry
