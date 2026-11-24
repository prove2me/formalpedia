-- Prove2me | Theorems.Thm_GlobalTheory_map_pi_eq_of_map_addHaar_eq
-- name    : GlobalTheory.map_pi_eq_of_map_addHaar_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:09:30.661341+00:00
-- url     : https://prove2.me/theorems/5b591235-1720-4432-9ed8-952a47275748
-- title:
--   Global Theory: map pi eq of map add Haar eq
-- statement:
--   The Global Theory construction uses the map pi eq of map add Haar eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MapPiEqOfMapAddHaarEq.lean#L6-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MapPiEqOfMapAddHaarEq.lean#L6-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MapPiEqOfMapAddHaarEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.map_pi_eq_of_map_addHaar_eq (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (φ : G →+ G) (hφ : Continuous φ)
    (h : ∀ ν : Measure G, ν.IsAddHaarMeasure → ν.map φ = ν) (m : ℕ)
    (μ : @Measure (Fin m → G) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (Fin m → G) _ _ (borel _) μ) :
    @Measure.map _ _ (borel _) (borel _) (fun x i => φ (x i)) μ = μ := by sorry
