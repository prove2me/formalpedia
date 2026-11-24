-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnitInd_lintegral_KO_mul_right
-- name    : GlobalTheory.SmGL.UnitInd.lintegral_KO_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:26.661591+00:00
-- url     : https://prove2.me/theorems/fb681fb2-ce78-4395-a2c7-46a653d18e34
-- title:
--   Unit Ind: lintegral KO mul right
-- statement:
--   The Unit Ind construction uses the lintegral KO mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L299-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L299-L402

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
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
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SmGL.UnitInd.lintegral_KO_mul_right (μ : Measure (GL n k)) [μ.IsHaarMeasure] {φ : GL n k → ℝ≥0∞} (hφ : Measurable φ)
    (hlaw : ∀ (p : parab k e) x, φ (p * x) = ENNReal.ofReal (modulus k m (leviProj k e p)) * φ x) (g : GL n k) :
    ∫⁻ x in (KO k n : Set (GL n k)), φ (x * g) ∂μ = ∫⁻ x in (KO k n : Set (GL n k)), φ x ∂μ := by sorry
