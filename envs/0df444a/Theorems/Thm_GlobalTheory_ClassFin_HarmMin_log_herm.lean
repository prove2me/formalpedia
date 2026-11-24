-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_HarmMin_log_herm
-- name    : GlobalTheory.ClassFin.HarmMin.log_herm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:19.303973+00:00
-- url     : https://prove2.me/theorems/8c662336-a6cf-4166-b878-f05f808b3cee
-- title:
--   Harm Min: log herm
-- statement:
--   The Harm Min construction uses the log herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SumHermitianLogGramEqZeroOfEnergyMinimum.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SumHermitianLogGramEqZeroOfEnergyMinimum.lean#L15-L19

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

theorem GlobalTheory.ClassFin.HarmMin.log_herm {H A : Matrix ι ι ℂ} (h : IsLog H A) : Hᴴ = H := by sorry
