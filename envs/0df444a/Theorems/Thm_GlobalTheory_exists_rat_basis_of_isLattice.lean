-- Prove2me | Theorems.Thm_GlobalTheory_exists_rat_basis_of_isLattice
-- name    : GlobalTheory.exists_rat_basis_of_isLattice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:58.134928+00:00
-- url     : https://prove2.me/theorems/ddad6098-88c2-4d83-b7fb-338350d41d17
-- title:
--   Global Theory: exists rat basis of is Lattice
-- statement:
--   The Global Theory construction uses the exists rat basis of is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L326-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L326-L357

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
variable {G : Matrix (Fin r) (Fin r) E} {Λ Λ₁ Λ₂ : Submodule (𝓞 E) (Fin r → E)}
omit [IsCMField E]

theorem GlobalTheory.exists_rat_basis_of_isLattice (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ (Fin r → E)),
      Submodule.span ℤ (Set.range b) = Λ.restrictScalars ℤ := by sorry
