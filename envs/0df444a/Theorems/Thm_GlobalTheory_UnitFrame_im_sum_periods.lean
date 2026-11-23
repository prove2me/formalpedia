-- Prove2me | Theorems.Thm_GlobalTheory_UnitFrame_im_sum_periods
-- name    : GlobalTheory.UnitFrame.im_sum_periods
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:39.929805+00:00
-- url     : https://prove2.me/theorems/f56413a8-e221-47eb-a4aa-aae4672d8f10
-- title:
--   Unit Frame: im sum periods
-- statement:
--   The Unit Frame construction uses the im sum periods property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemIffConjugateNotMem.lean#L91-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemIffConjugateNotMem.lean#L91-L133

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemIffConjugateNotMem
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
open GlobalTheory GlobalTheory.UnitFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.UnitFrame.im_sum_periods {r : ℕ} (q : ℕ) (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ)
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ))
    (u v : Fin r → ℂ) :
    (∑ a : Fin r, (if (a : ℕ) < q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) u else (x⁻¹ *ᵥ u) a) *
      conj (if (a : ℕ) < q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) v else (x⁻¹ *ᵥ v) a)).im =
      -(_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v).im := by sorry
