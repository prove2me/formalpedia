-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSection_mem_finiteIntegralUnits_iff_forall_finUnitAt
-- name    : GroundTheory.Automorphic.GodementSection.mem_finiteIntegralUnits_iff_forall_finUnitAt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:59.547891+00:00
-- url     : https://prove2.me/theorems/3fb9eea1-08d6-518c-bb3e-97f6da1e55c5
-- title:
--   Godement Section: mem finite Integral Units iff forall fin Unit At
-- statement:
--   The Godement Section construction uses the mem finite Integral Units iff forall fin Unit At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L93-L96

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
variable (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Automorphic.GodementSection.mem_finiteIntegralUnits_iff_forall_finUnitAt (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    b ∈ finiteIntegralUnits K ↔ ∀ w : HeightOneSpectrum (𝓞 K), finUnitAt w b ∈ intUnitsAt w := by sorry
