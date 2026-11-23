-- Prove2me | Theorems.Thm_GlobalTheory_FramePeriod_allPer_apply
-- name    : GlobalTheory.FramePeriod.allPer_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:18.446039+00:00
-- url     : https://prove2.me/theorems/e0f37027-3b38-490e-a3ca-f1174d4a6a75
-- title:
--   Frame Period: all Per apply
-- statement:
--   The Frame Period construction uses the all Per apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L325-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L325-L327

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

theorem GlobalTheory.FramePeriod.allPer_apply {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (x : FD.Frame Ψ r)
    {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (y : Ψ → Fin r → ℂ) (k : Fin g) : allPer Gm q x idx y k =
      locPer (idx k).1.1 Gm q (FD.mat x (idx k).1) (y (idx k).1) (idx k).2 := by sorry
