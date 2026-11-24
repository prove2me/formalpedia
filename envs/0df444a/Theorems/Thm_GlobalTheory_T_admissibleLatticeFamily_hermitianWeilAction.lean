-- Prove2me | Theorems.Thm_GlobalTheory_T_admissibleLatticeFamily_hermitianWeilAction
-- name    : GlobalTheory.T.admissibleLatticeFamily_hermitianWeilAction
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:37.095673+00:00
-- url     : https://prove2.me/theorems/42868863-5f31-4d02-a52f-658140acee1b
-- title:
--   T: admissible Lattice Family hermitian Weil Action
-- statement:
--   The T construction uses the admissible Lattice Family hermitian Weil Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/AdmissibleLatticeFamilyHermitianWeilActionStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/AdmissibleLatticeFamilyHermitianWeilActionStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilActionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.admissibleLatticeFamily_hermitianWeilAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ c R : ℕ, 0 < c → ∃ R' : ℕ, ∀ (M : ℕ) (φ : Fam E n N), admitted M R φ → ∀ γ ∈ UU E N, Den c γ → admitted M R' (fun Λ => weil Ψ γ (φ Λ)) := by sorry
