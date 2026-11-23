-- Prove2me | Theorems.Thm_GlobalTheory_HeckeStrip_classPartFun_mul_wt
-- name    : GlobalTheory.HeckeStrip.classPartFun_mul_wt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:14.29313+00:00
-- url     : https://prove2.me/theorems/f834388b-06fb-423b-8365-cc72a50a6a7f
-- title:
--   Hecke Strip: class Part Fun mul wt
-- statement:
--   The Hecke Strip construction uses the class Part Fun mul wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeLSeriesEqSumPrincipalPartialSeries.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeLSeriesEqSumPrincipalPartialSeries.lean#L62-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeStrip
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
variable {φ : I → K →+* ℂ} {n : I → ℤ} {m : Ideal (𝓞 K)} {X : Ideal (𝓞 K) → ℂ}

theorem GlobalTheory.HeckeStrip.classPartFun_mul_wt
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) {α : 𝓞 K} (hα : α ≠ 0) :
    classPartFun φ n m X b α * wt φ n (α : K) = open Classical in if α ∈ b then X (Ideal.span {α}) else 0 := by sorry
