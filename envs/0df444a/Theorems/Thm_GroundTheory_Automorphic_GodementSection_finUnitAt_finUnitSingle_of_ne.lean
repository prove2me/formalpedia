-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSection_finUnitAt_finUnitSingle_of_ne
-- name    : GroundTheory.Automorphic.GodementSection.finUnitAt_finUnitSingle_of_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:47.364262+00:00
-- url     : https://prove2.me/theorems/1b47d28a-8008-5548-bbe3-a54e48816b8e
-- title:
--   Godement Section: fin Unit At fin Unit Single of ne
-- statement:
--   The Godement Section construction uses the fin Unit At fin Unit Single of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L48-L50

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

theorem GroundTheory.Automorphic.GodementSection.finUnitAt_finUnitSingle_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (a : (v.adicCompletion K)ˣ) : finUnitAt w (finUnitSingle v a) = 1 := by sorry
