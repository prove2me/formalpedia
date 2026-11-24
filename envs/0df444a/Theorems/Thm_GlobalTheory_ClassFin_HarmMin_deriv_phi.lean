-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_HarmMin_deriv_phi
-- name    : GlobalTheory.ClassFin.HarmMin.deriv_phi
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:11.763287+00:00
-- url     : https://prove2.me/theorems/90c59dab-904a-4aad-b317-f4c966f6d22d
-- title:
--   Harm Min: deriv phi
-- statement:
--   The Harm Min construction uses the deriv phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SumHermitianLogGramEqZeroOfEnergyMinimum.lean#L56-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SumHermitianLogGramEqZeroOfEnergyMinimum.lean#L56-L69

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

theorem GlobalTheory.ClassFin.HarmMin.deriv_phi {Y : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} (h : HasDerivAt Y D 0) (h0 : Y 0 = 0)
    (M : Matrix ι ι ℂ) (C : ℝ) :
    HasDerivAt (fun t => 2 * (Matrix.trace (M * Y t)).re + C * ∑ i, ∑ j, ‖Y t i j‖ ^ 2)
      (2 * (Matrix.trace (M * D)).re) 0 := by sorry
