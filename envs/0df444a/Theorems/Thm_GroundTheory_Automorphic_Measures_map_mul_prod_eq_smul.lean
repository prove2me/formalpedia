-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_map_mul_prod_eq_smul
-- name    : GroundTheory.Automorphic.Measures.map_mul_prod_eq_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:09.61311+00:00
-- url     : https://prove2.me/theorems/f1cad933-9e88-5195-96fb-12906b747e9b
-- title:
--   Measures: map mul prod eq smul
-- statement:
--   The Measures construction uses the map mul prod eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Measures.lean#L89-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Measures.lean#L89-L214

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (K : Subgroup G)
variable {K}

theorem GroundTheory.Automorphic.Measures.map_mul_prod_eq_smul [TotallyDisconnectedSpace G] (P K : Subgroup G)
    (hP : IsClosed (P : Set G))
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (μG : Measure G) [μG.IsHaarMeasure] (μP : Measure P) [μP.IsHaarMeasure] (μK : Measure K)
    [μK.IsHaarMeasure] :
    μG K • map (fun x : P × K => (x.1 : G) * x.2) (μP.prod μK) =
      (μP (Subtype.val ⁻¹' (K : Set G)) * μK univ) • μG := by sorry
