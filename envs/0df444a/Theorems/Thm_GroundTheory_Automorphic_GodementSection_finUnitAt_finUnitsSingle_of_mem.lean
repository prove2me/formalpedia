-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSection_finUnitAt_finUnitsSingle_of_mem
-- name    : GroundTheory.Automorphic.GodementSection.finUnitAt_finUnitsSingle_of_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:50:21.326485+00:00
-- url     : https://prove2.me/theorems/631af7d5-dabf-44f2-88e1-56fcdf9f75ec
-- title:
--   Godement Section: fin Unit At fin Units Single of mem
-- statement:
--   The Godement Section construction uses the fin Unit At fin Units Single of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L125-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L125-L134

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

theorem GroundTheory.Automorphic.GodementSection.finUnitAt_finUnitsSingle_of_mem (a : (v : S) → (v.1.adicCompletion K)ˣ) (w : S) :
    finUnitAt w.1 (finUnitsSingle S a) = a w := by sorry
