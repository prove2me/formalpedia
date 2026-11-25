-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSection_finUnitAt_mem_intUnitsAt_iff
-- name    : GroundTheory.Automorphic.GodementSection.finUnitAt_mem_intUnitsAt_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:44.847564+00:00
-- url     : https://prove2.me/theorems/92a4151e-bca0-59a2-b43d-36689b03e2df
-- title:
--   Godement Section: fin Unit At mem int Units At iff
-- statement:
--   The Godement Section construction uses the fin Unit At mem int Units At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L87-L91

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

theorem GroundTheory.Automorphic.GodementSection.finUnitAt_mem_intUnitsAt_iff (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    finUnitAt v b ∈ intUnitsAt v ↔ (b : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
      ((b⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
        v.adicCompletionIntegers K := by sorry
