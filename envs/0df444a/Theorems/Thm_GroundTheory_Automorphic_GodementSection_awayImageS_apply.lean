-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSection_awayImageS_apply
-- name    : GroundTheory.Automorphic.GodementSection.awayImageS_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:02.20329+00:00
-- url     : https://prove2.me/theorems/9d538e47-5e41-437e-b144-dd3c9dd3ed7f
-- title:
--   Godement Section: away Image S apply
-- statement:
--   The Godement Section construction uses the away Image S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L174-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L174-L178

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
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {S}

theorem GroundTheory.Automorphic.GodementSection.awayImageS_apply (g : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)
    {A : Set ((v : S) → (v.1.adicCompletion K)ˣ)} (hA : MeasurableSet A) :
    awayImageS S g A = ∫⁻ b, (finUnitsAt S ⁻¹' A).indicator g b ∂finiteIdeleMeasure K := by sorry
