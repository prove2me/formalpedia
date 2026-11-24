-- Prove2me | Theorems.Thm_GlobalTheory_HeckeStrip_pval_classPartFun
-- name    : GlobalTheory.HeckeStrip.pval_classPartFun
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:50.151867+00:00
-- url     : https://prove2.me/theorems/950f8132-a1bc-4514-bad9-9a8eef537221
-- title:
--   Hecke Strip: pval class Part Fun
-- statement:
--   The Hecke Strip construction uses the pval class Part Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeLSeriesEqSumPrincipalPartialSeries.lean#L160-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeLSeriesEqSumPrincipalPartialSeries.lean#L160-L173

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

theorem GlobalTheory.HeckeStrip.pval_classPartFun
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b J : Ideal (𝓞 K)) [J.IsPrincipal] (hJ : J ≠ ⊥) :
    pval (classPartFun φ n m X b) φ n J = open Classical in if J ≤ b then X J else 0 := by sorry
