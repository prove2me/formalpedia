-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_LeviInt_levi_integral_facts
-- name    : GlobalTheory.SmGL.LeviInt.levi_integral_facts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:25.209152+00:00
-- url     : https://prove2.me/theorems/ee59c396-395d-44a7-bd9b-4e7ad912f50c
-- title:
--   Levi Int: levi integral facts
-- statement:
--   The Levi Int construction uses the levi integral facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeviIntegralFacts.lean#L44-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeviIntegralFacts.lean#L44-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.LeviInt
open MeasureTheory Topology
open scoped ENNReal

theorem GlobalTheory.SmGL.LeviInt.levi_integral_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n), (∀ (g : _root_.GlobalTheory.SmGL.Levi k m) (u : GL n k), u ∈ _root_.GlobalTheory.SmGL.unipRad k e → (_root_.GlobalTheory.SmGL.leviEmb k e g * u ∈ _root_.GlobalTheory.SplitWeil.KO k n ↔ (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧ u ∈ _root_.GlobalTheory.SplitWeil.KO k n)) ∧ (∀ p : _root_.GlobalTheory.SmGL.parab k e, (p : GL n k) ∈ _root_.GlobalTheory.SplitWeil.KO k n → ∀ a, _root_.GlobalTheory.SmGL.leviProj k e p a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧ (∀ g : _root_.GlobalTheory.SmGL.Levi k m, (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) → _root_.GlobalTheory.SmGL.modulus k m g = 1) ∧ (∀ g h : _root_.GlobalTheory.SmGL.Levi k m, _root_.GlobalTheory.SmGL.modulus k m (g * h) = _root_.GlobalTheory.SmGL.modulus k m g * _root_.GlobalTheory.SmGL.modulus k m h) ∧ Continuous (_root_.GlobalTheory.SmGL.modulus k m) ∧ Continuous (_root_.GlobalTheory.SmGL.leviProj k e) ∧ IsClosed (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) ∧ IsClosed (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) ∧ ∀ g : GL n k, ∃ p ∈ _root_.GlobalTheory.SmGL.parab k e, ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, g = p * x := by sorry
