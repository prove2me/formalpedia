-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_HarmMin_trace_id
-- name    : GlobalTheory.ClassFin.HarmMin.trace_id
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:10.525809+00:00
-- url     : https://prove2.me/theorems/c385fb0f-e3e5-433d-b8a7-72a26a65f271
-- title:
--   Harm Min: trace id
-- statement:
--   The Harm Min construction uses the trace id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SumHermitianLogGramEqZeroOfEnergyMinimum.lean#L71-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SumHermitianLogGramEqZeroOfEnergyMinimum.lean#L71-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HermitianLogTraceSqFirstVariationBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MulLogEqNegLogMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsHermitianLogOfPosDefGramStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SumHermitianLogGramEqZeroOfEnergyMinimum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.HarmMin
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.ClassFin.HarmMin.trace_id {g g' H H' X : Matrix ι ι ℂ} (hg : g' * g = 1) (hc : (gᴴ * g) * H = H * (gᴴ * g))
    (hi : g * H = -(H' * g)) :
    Matrix.trace (H * (gᴴ * g)⁻¹ * (-X * (gᴴ * g) + gᴴ * X * g + gᴴ * X * g - (gᴴ * g) * X)) =
      -2 * Matrix.trace (H * X) - 2 * Matrix.trace (H' * X) := by sorry
