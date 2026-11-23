-- Prove2me | Theorems.Thm_GlobalTheory_HeckeStrip_wt_ne_zero_of_ne_zero
-- name    : GlobalTheory.HeckeStrip.wt_ne_zero_of_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:36.688607+00:00
-- url     : https://prove2.me/theorems/e40fa112-6474-44b1-8d1b-ec987b892054
-- title:
--   Hecke Strip: wt ne zero of ne zero
-- statement:
--   The Hecke Strip construction uses the wt ne zero of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeLSeriesEqSumPrincipalPartialSeries.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeLSeriesEqSumPrincipalPartialSeries.lean#L51-L56

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

theorem GlobalTheory.HeckeStrip.wt_ne_zero_of_ne_zero (φ : I → K →+* ℂ) (n : I → ℤ) {α : 𝓞 K} (hα : α ≠ 0) : wt φ n (α : K) ≠ 0 := by sorry
