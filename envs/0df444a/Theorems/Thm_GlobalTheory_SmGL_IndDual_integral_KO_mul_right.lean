-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IndDual_integral_KO_mul_right
-- name    : GlobalTheory.SmGL.IndDual.integral_KO_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:51.799783+00:00
-- url     : https://prove2.me/theorems/7e4e314f-446d-4eb9-9c7c-c081cd132764
-- title:
--   Ind Dual: integral KO mul right
-- statement:
--   The Ind Dual construction uses the integral KO mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralIntegralGLMulRightComplexProductSigma.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralIntegralGLMulRightComplexProductSigma.lean#L53-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
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
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndDual

theorem GlobalTheory.SmGL.IndDual.integral_KO_mul_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure] (F : GL n k → ℂ), Continuous F → (∀ (p : parab k e) (g : GL n k), F (p * g) = (modulus k m (leviProj k e p) : ℂ) * F g) → ∀ g : GL n k, ∫ x in (KO k n : Set (GL n k)), F (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), F x ∂μ := by sorry
