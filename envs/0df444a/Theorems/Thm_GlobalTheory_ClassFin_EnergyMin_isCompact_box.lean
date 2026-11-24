-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_EnergyMin_isCompact_box
-- name    : GlobalTheory.ClassFin.EnergyMin.isCompact_box
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:08:57.616119+00:00
-- url     : https://prove2.me/theorems/ca4dceb6-6ab6-433d-a9d1-c61120f6bbe3
-- title:
--   Energy Min: is Compact box
-- statement:
--   The Energy Min construction uses the is Compact box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEnergyMin.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEnergyMin.lean#L28-L36

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
omit [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.ClassFin.EnergyMin.isCompact_box (C : ℝ) : IsCompact {x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C} := by sorry
