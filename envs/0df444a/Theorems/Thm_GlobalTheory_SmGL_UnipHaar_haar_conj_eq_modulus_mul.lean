-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_haar_conj_eq_modulus_mul
-- name    : GlobalTheory.SmGL.UnipHaar.haar_conj_eq_modulus_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:12.557281+00:00
-- url     : https://prove2.me/theorems/3838df4d-700d-4682-b82e-103b02db970c
-- title:
--   Unip Haar: haar conj eq modulus mul
-- statement:
--   The Unip Haar construction uses the haar conj eq modulus mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L294-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L294-L318

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar

theorem GlobalTheory.SmGL.UnipHaar.haar_conj_eq_modulus_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] (μ : Measure (unipRad k e)) [μ.IsHaarMeasure] (g : Levi k m) (S : Set (unipRad k e)), MeasurableSet S → μ {u | ∃ s ∈ S, (u : GL n k) = leviEmb k e g * (s : GL n k) * (leviEmb k e g)⁻¹} = ENNReal.ofReal (modulus k m g) * μ S := by sorry
