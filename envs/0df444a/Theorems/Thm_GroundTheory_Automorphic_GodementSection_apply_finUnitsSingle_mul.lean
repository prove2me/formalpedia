-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSection_apply_finUnitsSingle_mul
-- name    : GroundTheory.Automorphic.GodementSection.apply_finUnitsSingle_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:31.772705+00:00
-- url     : https://prove2.me/theorems/5c075f25-349e-4d15-b9f7-dcb300267737
-- title:
--   Godement Section: apply fin Units Single mul
-- statement:
--   The Godement Section construction uses the apply fin Units Single mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L147-L151

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

theorem GroundTheory.Automorphic.GodementSection.apply_finUnitsSingle_mul {E : Type*} {G : (FiniteAdeleRing (𝓞 K) K)ˣ → E}
    (hG : ∀ b b', (∀ w ∉ S, finUnitAt w b = finUnitAt w b') → G b = G b')
    (a : (v : S) → (v.1.adicCompletion K)ˣ) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    G (finUnitsSingle S a * b) = G b := by sorry
