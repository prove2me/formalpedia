-- Prove2me | Theorems.Thm_GlobalTheory_isLattice_fractionalIdeal_smul
-- name    : GlobalTheory.isLattice_fractionalIdeal_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:25.742364+00:00
-- url     : https://prove2.me/theorems/ef41c9a0-5734-4a00-9cae-073d20189755
-- title:
--   Global Theory: is Lattice fractional Ideal smul
-- statement:
--   The Global Theory construction uses the is Lattice fractional Ideal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L130-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L130-L163

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [IsCMField E]

theorem GlobalTheory.isLattice_fractionalIdeal_smul {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0)
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice ((a : Submodule (𝓞 E) E) • Λ) := by sorry
