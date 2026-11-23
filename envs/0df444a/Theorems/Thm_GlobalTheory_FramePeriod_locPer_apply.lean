-- Prove2me | Theorems.Thm_GlobalTheory_FramePeriod_locPer_apply
-- name    : GlobalTheory.FramePeriod.locPer_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:15.563614+00:00
-- url     : https://prove2.me/theorems/f87d4733-4222-4711-8080-1a5f615fc839
-- title:
--   Frame Period: loc Per apply
-- statement:
--   The Frame Period construction uses the loc Per apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L86-L88

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

theorem GlobalTheory.FramePeriod.locPer_apply (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → ℂ) (a : Fin r) : locPer τ Gm q M u a =
      if (a : ℕ) < q then FD.hermC τ Gm (FD.col M a) u else (M⁻¹ *ᵥ u) a := by sorry
