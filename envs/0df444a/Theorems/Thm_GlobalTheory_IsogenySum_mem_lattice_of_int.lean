-- Prove2me | Theorems.Thm_GlobalTheory_IsogenySum_mem_lattice_of_int
-- name    : GlobalTheory.IsogenySum.mem_lattice_of_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:09:46.767841+00:00
-- url     : https://prove2.me/theorems/f5700beb-db23-48cf-93aa-48e52d3fae24
-- title:
--   Isogeny Sum: mem lattice of int
-- statement:
--   The Isogeny Sum construction uses the mem lattice of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ContinuousThetaSectionPointwiseNormSq.lean#L38-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ContinuousThetaSectionPointwiseNormSq.lean#L38-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open GlobalTheory.IsogenySum
open FockTranslation
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.IsogenySum.mem_lattice_of_int (Y : GT ι) {a : EuclideanSpace ℂ ι}
    (h : ∀ y ∈ lat Y.b, ∃ k : ℤ, (Hf y a).im = k) : a ∈ lat Y.b := by sorry
