-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_fderiv_comp_clm
-- name    : GlobalTheory.RealWeil.UnitaryOsc.fderiv_comp_clm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:28.819794+00:00
-- url     : https://prove2.me/theorems/7d316b24-8e8e-4d30-8a1c-3d64aaca6b61
-- title:
--   Unitary Osc: fderiv comp clm
-- statement:
--   The Unitary Osc construction uses the fderiv comp clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionUnitaryGroupHermitian.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionUnitaryGroupHermitian.lean#L29-L34

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
variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem GlobalTheory.RealWeil.UnitaryOsc.fderiv_comp_clm {ρ : V' → B →L[ℂ] B} {f : B} (hf : Sm ρ f) (E : V →L[ℝ] V') (z : V) :
    fderiv ℝ (fun v => ρ (E v) f) 0 z = fderiv ℝ (fun v => ρ v f) 0 (E z) := by sorry
