-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_omJ_cplx
-- name    : GlobalTheory.RealWeil.UnitaryOsc.omJ_cplx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:58.746953+00:00
-- url     : https://prove2.me/theorems/1da39940-752a-44b2-8f8b-6e46dc5b145a
-- title:
--   Unitary Osc: om J cplx
-- statement:
--   The Unitary Osc construction uses the om J cplx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionUnitaryGroupHermitian.lean#L136-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionUnitaryGroupHermitian.lean#L136-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairingsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartanInvolutionConjOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianCongrInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.UnitaryOsc
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.RealWeil.UnitaryOsc.omJ_cplx (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) (x y : EuclideanSpace ℂ ι) :
    omJ (cplx s h1 h2) x y = (star (crd ι y) ⬝ᵥ s *ᵥ crd ι x).im := by sorry
