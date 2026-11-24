-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_EnergyMin_inv_eq_adj
-- name    : GlobalTheory.ClassFin.EnergyMin.inv_eq_adj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:31.436411+00:00
-- url     : https://prove2.me/theorems/5962c55e-b5fa-4e15-b498-670fb5f66e14
-- title:
--   Energy Min: inv eq adj
-- statement:
--   The Energy Min construction uses the inv eq adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEnergyMin.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEnergyMin.lean#L55-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EntriesBoundedOfConjSpanningBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsClosedIsHermitianLogOfPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MatrixEntriesBoundedOfHermitianLogTraceSqLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsHermitianLogOfPosDefGramStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEnergyMin
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
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.EnergyMin
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.ClassFin.EnergyMin.inv_eq_adj {P : Matrix ι ι ℂ} (hP : P.det = 1) : P⁻¹ = P.adjugate := by sorry
