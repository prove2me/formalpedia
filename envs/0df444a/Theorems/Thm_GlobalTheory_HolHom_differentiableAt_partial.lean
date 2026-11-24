-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_differentiableAt_partial
-- name    : GlobalTheory.HolHom.differentiableAt_partial
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:36:25.900316+00:00
-- url     : https://prove2.me/theorems/42ba59c0-d77f-498f-a81f-34d65ae71c65
-- title:
--   Hol Hom: differentiable At partial
-- statement:
--   The Hol Hom construction uses the differentiable At partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L531-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L531-L541

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {S : Scheme.{0}} {G : Over S} {g : ℕ}

theorem GlobalTheory.HolHom.differentiableAt_partial {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [FiniteDimensional ℂ V] {F : P × V → ℂ} {s : Set (P × V)} (hs : IsOpen s) (hF : DifferentiableOn ℂ F s) {b : P}
    (hb : (b, 0) ∈ s) : DifferentiableAt ℂ (fun b => fderiv ℂ (fun z => F (b, z)) 0) b := by sorry
