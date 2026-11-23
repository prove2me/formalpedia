-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_HarmMin_deriv_entry
-- name    : GlobalTheory.ClassFin.HarmMin.deriv_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:45:47.258517+00:00
-- url     : https://prove2.me/theorems/284206b4-1bb4-45f5-883f-bf7145ba728b
-- title:
--   Harm Min: deriv entry
-- statement:
--   The Harm Min construction uses the deriv entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SumHermitianLogGramEqZeroOfEnergyMinimum.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SumHermitianLogGramEqZeroOfEnergyMinimum.lean#L51-L54

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

theorem GlobalTheory.ClassFin.HarmMin.deriv_entry {Y : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} (h : HasDerivAt Y D 0) (i j : ι) :
    HasDerivAt (fun t => Y t i j) (D i j) 0 := by sorry
