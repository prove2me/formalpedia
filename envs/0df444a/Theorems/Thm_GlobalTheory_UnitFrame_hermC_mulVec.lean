-- Prove2me | Theorems.Thm_GlobalTheory_UnitFrame_hermC_mulVec
-- name    : GlobalTheory.UnitFrame.hermC_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:08.944119+00:00
-- url     : https://prove2.me/theorems/f0e445f9-5a30-4b8c-804d-6830c2e487eb
-- title:
--   Unit Frame: herm C mul Vec
-- statement:
--   The Unit Frame construction uses the herm C mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemIffConjugateNotMem.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemIffConjugateNotMem.lean#L77-L84

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

theorem GlobalTheory.UnitFrame.hermC_mulVec {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) (c c' : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (x *ᵥ c) (x *ᵥ c') = c ⬝ᵥ (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x) *ᵥ (star c') := by sorry
