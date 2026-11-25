-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSection_isFiniteMeasureOnCompacts_awayImageS
-- name    : GroundTheory.Automorphic.GodementSection.isFiniteMeasureOnCompacts_awayImageS
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:48:01.29458+00:00
-- url     : https://prove2.me/theorems/a749a105-825f-518c-9674-a3cbbcd939cc
-- title:
--   Godement Section: is Finite Measure On Compacts away Image S
-- statement:
--   The Godement Section construction uses the is Finite Measure On Compacts away Image S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L194-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/FiniteIdeleDecomp.lean#L194-L211

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

theorem GroundTheory.Automorphic.GodementSection.isFiniteMeasureOnCompacts_awayImageS {g : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ≥0∞}
    (hinv : ∀ a b, g (finUnitsSingle S a * b) = g b) (hc : awayImageS S g (intUnitsAtS S) ≠ ∞) :
    IsFiniteMeasureOnCompacts (awayImageS S g) := by sorry
