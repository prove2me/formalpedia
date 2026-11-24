-- Prove2me | Theorems.Thm_GlobalTheory_T_isSiegelUpperHalfSpace_neg_mul_inv_symplectic
-- name    : GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:49:56.722434+00:00
-- url     : https://prove2.me/theorems/68e6de84-6a42-46ea-adc0-302b9158f61c
-- title:
--   T: is Siegel Upper Half Space neg mul inv symplectic
-- statement:
--   The T construction uses the is Siegel Upper Half Space neg mul inv symplectic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSiegelUpperHalfSpaceNegMulInvSymplecticStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSiegelUpperHalfSpaceNegMulInvSymplecticStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSiegelUpperHalfSpaceNegMulInvSymplectic
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSiegelUpperHalfSpaceNegMulInvSymplecticStatement
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

theorem GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 → (-(Q * P⁻¹)).IsSymm → GlobalTheory.IsSiegel (-(Q * P⁻¹)) := by sorry
