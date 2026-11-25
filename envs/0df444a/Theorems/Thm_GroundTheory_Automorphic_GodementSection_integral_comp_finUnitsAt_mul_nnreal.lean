-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSection_integral_comp_finUnitsAt_mul_nnreal
-- name    : GroundTheory.Automorphic.GodementSection.integral_comp_finUnitsAt_mul_nnreal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:51:58.41438+00:00
-- url     : https://prove2.me/theorems/a7e29bef-bf76-4a1e-9b79-5724ac181c5f
-- title:
--   Godement Section: integral comp fin Units At mul nnreal
-- statement:
--   The Godement Section construction uses the integral comp fin Units At mul nnreal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L234-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L234-L280

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

theorem GroundTheory.Automorphic.GodementSection.integral_comp_finUnitsAt_mul_nnreal {g : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ≥0}
    (hg : Measurable g) (hinv : ∀ a b, g (finUnitsSingle S a * b) = g b)
    (hgi : Integrable ((finUnitsAt S ⁻¹' intUnitsAtS S).indicator fun b ↦ (g b : ℝ))
      (finiteIdeleMeasure K))
    {F : ((v : S) → (v.1.adicCompletion K)ˣ) → ℂ} (hF : Integrable F (multHaarS S)) :
    Integrable (fun b ↦ F (finUnitsAt S b) * ((g b : ℝ) : ℂ)) (finiteIdeleMeasure K) ∧
      ∫ b, F (finUnitsAt S b) * ((g b : ℝ) : ℂ) ∂finiteIdeleMeasure K =
        (∫ a, F a ∂multHaarS S) *
          ((∫ b, (finUnitsAt S ⁻¹' intUnitsAtS S).indicator (fun b ↦ (g b : ℝ)) b
            ∂finiteIdeleMeasure K : ℝ) : ℂ) := by sorry
