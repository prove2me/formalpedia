-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSection_measurable_finUnitAt
-- name    : GroundTheory.Automorphic.GodementSection.measurable_finUnitAt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:05:00.271145+00:00
-- url     : https://prove2.me/theorems/8b68baf1-42fe-56c4-af4c-2cd613516047
-- title:
--   Godement Section: measurable fin Unit At
-- statement:
--   The Godement Section construction uses the measurable fin Unit At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L34-L35

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

theorem GroundTheory.Automorphic.GodementSection.measurable_finUnitAt (v : HeightOneSpectrum (𝓞 K)) : Measurable (finUnitAt (K := K) v) := by sorry
