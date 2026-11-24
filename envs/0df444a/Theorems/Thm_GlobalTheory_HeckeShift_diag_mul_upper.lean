-- Prove2me | Theorems.Thm_GlobalTheory_HeckeShift_diag_mul_upper
-- name    : GlobalTheory.HeckeShift.diag_mul_upper
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:04:44.20392+00:00
-- url     : https://prove2.me/theorems/20d72225-4ba4-43fb-8a26-46fa002098d9
-- title:
--   Hecke Shift: diag mul upper
-- statement:
--   The Hecke Shift construction uses the diag mul upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesSphericalEigenfunction.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesSphericalEigenfunction.lean#L55-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesBorelSphericalIntegralCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.HeckeShift
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.HeckeShift.diag_mul_upper {A B : Matrix (Fin n) (Fin n) k} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by sorry
