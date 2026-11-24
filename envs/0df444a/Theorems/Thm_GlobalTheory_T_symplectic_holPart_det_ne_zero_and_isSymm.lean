-- Prove2me | Theorems.Thm_GlobalTheory_T_symplectic_holPart_det_ne_zero_and_isSymm
-- name    : GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:56.153045+00:00
-- url     : https://prove2.me/theorems/b1321955-d694-4da5-9d75-df74bdd751ac
-- title:
--   T: symplectic hol Part det ne zero and is Symm
-- statement:
--   The T construction uses the symplectic hol Part det ne zero and is Symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymplecticHolPartDetNeZeroAndIsSymmStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymplecticHolPartDetNeZeroAndIsSymmStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticHolPartDetNeZeroAndIsSymm
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticHolPartDetNeZeroAndIsSymmStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 ∧ (-(Q * P⁻¹)).IsSymm := by sorry
