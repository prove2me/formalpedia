-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_fourier_prod_coord
-- name    : GlobalTheory.LipschitzTR.fourier_prod_coord
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:12:38.889796+00:00
-- url     : https://prove2.me/theorems/e9d4ec90-c32f-4a8b-a283-9c6a26428699
-- title:
--   Lipschitz TR: fourier prod coord
-- statement:
--   The Lipschitz TR construction uses the fourier prod coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LipschitzFormulaTotallyRealPoisson.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LipschitzFormulaTotallyRealPoisson.lean#L47-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImageStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsZLatticeFractionalIdealRealLatticeImageStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImageStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzFormulaTotallyRealPoisson
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.LipschitzTR
open GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.LipschitzTR.fourier_prod_coord (ι : Type) [Fintype ι] (f : ι → ℝ → ℂ) (x : EuclideanSpace ℝ ι) :
    𝓕 (fun ξ : EuclideanSpace ℝ ι => ∏ i, f i (ξ i)) x = ∏ i, 𝓕 (f i) (x i) := by sorry
