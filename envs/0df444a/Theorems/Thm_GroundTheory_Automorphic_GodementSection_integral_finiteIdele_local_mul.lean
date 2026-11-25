-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSection_integral_finiteIdele_local_mul
-- name    : GroundTheory.Automorphic.GodementSection.integral_finiteIdele_local_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:48.951212+00:00
-- url     : https://prove2.me/theorems/27238476-101c-4735-abcd-e2d9d14216d4
-- title:
--   Godement Section: integral finite Idele local mul
-- statement:
--   The Godement Section construction uses the integral finite Idele local mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L282-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L282-L366

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_FiniteIdeleDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology GroundTheory.Global GroundTheory.LocalField
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}

theorem GroundTheory.Automorphic.GodementSection.integral_finiteIdele_local_mul {F : ((v : S) → (v.1.adicCompletion K)ˣ) → ℂ}
    (hF : Integrable F (multHaarS S)) {G : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ} (hGm : Measurable G)
    (hG : ∀ b b', (∀ w ∉ S, finUnitAt w b = finUnitAt w b') → G b = G b')
    (hGi : Integrable ((finUnitsAt S ⁻¹' intUnitsAtS S).indicator G) (finiteIdeleMeasure K)) :
    Integrable (fun b ↦ F (finUnitsAt S b) * G b) (finiteIdeleMeasure K) ∧
      ∫ b, F (finUnitsAt S b) * G b ∂finiteIdeleMeasure K =
        (∫ a, F a ∂multHaarS S) *
          ∫ b, (finUnitsAt S ⁻¹' intUnitsAtS S).indicator G b ∂finiteIdeleMeasure K := by sorry
