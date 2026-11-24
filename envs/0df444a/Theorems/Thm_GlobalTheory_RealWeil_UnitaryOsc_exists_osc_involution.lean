-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_exists_osc_involution
-- name    : GlobalTheory.RealWeil.UnitaryOsc.exists_osc_involution
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:17:41.598803+00:00
-- url     : https://prove2.me/theorems/cc8955b9-6453-43a9-8e0c-78818cc791a8
-- title:
--   Unitary Osc: exists osc involution
-- statement:
--   The Unitary Osc construction uses the exists osc involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionUnitaryGroupHermitian.lean#L163-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionUnitaryGroupHermitian.lean#L163-L243

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

theorem GlobalTheory.RealWeil.UnitaryOsc.exists_osc_involution (H : Matrix ι ι ℂ) (h1 : Hᴴ = H) (h2 : H * H = 1) (B : Type) [NormedAddCommGroup B]
    [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B) (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ)
    (G : Type) [Group G] (m : G →* Matrix ι ι ℂ) (hm : ∀ g, (m g)ᴴ * H * m g = H) :
    ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∀ g, m g = 1 → ∀ f, Sm ρ f → Ω g f = f) ∧
      (∀ [TopologicalSpace G], Continuous m → ∀ f, Sm ρ f → Continuous fun g => Ω g f) ∧
      ∀ (s : Matrix ι ι ℂ) (g : G), s * s = 1 → (H * s).PosDef → s * m g = m g * s → ∀ f, Sm ρ f →
        (∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (I • s *ᵥ z) = 0) →
        Ω g f = dP s (m g) • f := by sorry
