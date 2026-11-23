-- Prove2me | Theorems.Thm_GlobalTheory_QFam_isMF_of_invariant_of_hasQ
-- name    : GlobalTheory.QFam.isMF_of_invariant_of_hasQ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:00.523127+00:00
-- url     : https://prove2.me/theorems/9691430e-c651-4b05-b88f-ebe53d8f2e63
-- title:
--   QFam: is MF of invariant of has Q
-- statement:
--   The QFam construction uses the is MF of invariant of has Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsModularFormLevelOneOfInvariantQExpansion.lean#L16-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsModularFormLevelOneOfInvariantQExpansion.lean#L16-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInftyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsModularFormLevelOneOfInvariantQExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

theorem GlobalTheory.QFam.isMF_of_invariant_of_hasQ : ∀ (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (a : ℕ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[k] γ = f) → _root_.GlobalTheory.QFam.HasQ N f a → _root_.ReciprocityTheory.ChartRestriction.L1.IsMF k f := by sorry
