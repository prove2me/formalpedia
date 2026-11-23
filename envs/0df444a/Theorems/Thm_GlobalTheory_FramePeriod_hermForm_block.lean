-- Prove2me | Theorems.Thm_GlobalTheory_FramePeriod_hermForm_block
-- name    : GlobalTheory.FramePeriod.hermForm_block
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:47.075795+00:00
-- url     : https://prove2.me/theorems/9e22d7d7-a41e-44ce-a3ec-c42664a91df4
-- title:
--   Frame Period: herm Form block
-- statement:
--   The Frame Period construction uses the herm Form block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L349-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L349-L363

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

theorem GlobalTheory.FramePeriod.hermForm_block {ι : Type} [Fintype ι] [DecidableEq ι] {g : ℕ} (idx : Fin g ≃ ι × Fin r)
    (s : ι → ℝ) (Hl : ι → Matrix (Fin r) (Fin r) ℂ) (z w : Fin g → ℂ) :
    hermForm (Matrix.of fun k l => if (idx k).1 = (idx l).1 then
      (s (idx k).1 : ℂ) * Hl (idx k).1 (idx k).2 (idx l).2 else 0) z w =
      ∑ τ, (s τ : ℂ) * hermForm (Hl τ) (fun a => z (idx.symm (τ, a))) (fun a => w (idx.symm (τ, a))) := by sorry
