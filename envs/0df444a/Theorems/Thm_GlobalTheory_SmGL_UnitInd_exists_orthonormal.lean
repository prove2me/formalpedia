-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnitInd_exists_orthonormal
-- name    : GlobalTheory.SmGL.UnitInd.exists_orthonormal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:13:58.97849+00:00
-- url     : https://prove2.me/theorems/b0dbf322-b305-4a17-bcf7-961eabc08c4d
-- title:
--   Unit Ind: exists orthonormal
-- statement:
--   The Unit Ind construction uses the exists orthonormal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L62-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L62-L73

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
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.SmGL.UnitInd.exists_orthonormal (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hs : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) {S : Set V}
    (hS : S.Finite) : ∃ (d : ℕ) (b : Fin d → V), (∀ i j, B (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ v ∈ S, ∃ c : Fin d → ℂ, v = ∑ i, c i • b i := by sorry
