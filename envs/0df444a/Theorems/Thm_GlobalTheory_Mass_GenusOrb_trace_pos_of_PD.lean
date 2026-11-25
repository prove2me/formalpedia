-- Prove2me | Theorems.Thm_GlobalTheory_Mass_GenusOrb_trace_pos_of_PD
-- name    : GlobalTheory.Mass.GenusOrb.trace_pos_of_PD
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:00:47.112117+00:00
-- url     : https://prove2.me/theorems/afbb5b6d-639c-5700-98ee-20c3c2ddcfe5
-- title:
--   Genus Orb: trace pos of PD
-- statement:
--   The Genus Orb construction uses the trace pos of PD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianGenusMassEqOrbitStabilizerMass.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianGenusMassEqOrbitStabilizerMass.lean#L19-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumEqSumOrbitReps
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianGenusMassEqOrbitStabilizerMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.GenusOrb
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
open NumberField Matrix
open scoped ENNReal Classical
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.Mass.GenusOrb.trace_pos_of_PD (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hp : _root_.GlobalTheory.Mass.PD h) (x : V) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (h x x) := by sorry
