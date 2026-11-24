-- Prove2me | Theorems.Thm_GlobalTheory_FramePeriod_hermForm_conj_diag
-- name    : GlobalTheory.FramePeriod.hermForm_conj_diag
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:39:11.050809+00:00
-- url     : https://prove2.me/theorems/225f1202-892a-4184-bcf2-98f214439331
-- title:
--   Frame Period: herm Form conj diag
-- statement:
--   The Frame Period construction uses the herm Form conj diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L90-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L90-L99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
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

theorem GlobalTheory.FramePeriod.hermForm_conj_diag {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ) (z w : Fin n → ℂ) :
    hermForm (Sᵀ * Matrix.diagonal (fun a => (e a : ℂ)) * S.map (starRingEnd ℂ)) z w =
      ∑ a, (e a : ℂ) * ((S *ᵥ z) a * conj ((S *ᵥ w) a)) := by sorry
