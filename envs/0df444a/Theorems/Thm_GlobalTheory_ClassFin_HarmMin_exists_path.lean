-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_HarmMin_exists_path
-- name    : GlobalTheory.ClassFin.HarmMin.exists_path
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:43.646485+00:00
-- url     : https://prove2.me/theorems/1a0cfde6-9abc-43b2-a8a9-09043d18979e
-- title:
--   Harm Min: exists path
-- statement:
--   The Harm Min construction uses the exists path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SumHermitianLogGramEqZeroOfEnergyMinimum.lean#L32-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SumHermitianLogGramEqZeroOfEnergyMinimum.lean#L32-L49

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

theorem GlobalTheory.ClassFin.HarmMin.exists_path (X : Matrix ι ι ℂ) (hX : Xᴴ = X) :
    ∃ P Q : ℝ → Matrix ι ι ℂ, P 0 = 1 ∧ Q 0 = 1 ∧ (∀ t, P t * Q t = 1) ∧ (∀ t, (P t)ᴴ = P t) ∧
      (∀ t, (Q t)ᴴ = Q t) ∧ HasDerivAt P X 0 ∧ HasDerivAt Q (-X) 0 := by sorry
