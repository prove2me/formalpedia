-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_holAt_lift
-- name    : GlobalTheory.HolHom.holAt_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:29.334534+00:00
-- url     : https://prove2.me/theorems/f4401c70-4cc6-41f6-acf0-762a1f9fc9d6
-- title:
--   Hol Hom: hol At lift
-- statement:
--   The Hol Hom construction uses the hol At lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L355-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L355-L361

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}}

theorem GlobalTheory.HolHom.holAt_lift {P : V → Over S} {G G' : Over S} (i : ∀ t, Sp ℂ ⟶ (P t).left) {a : ∀ t, P t ⟶ G}
    {b : ∀ t, P t ⟶ G'} {z : V} (ha : HolAt (fun t => i t ≫ (a t).left) z)
    (hb : HolAt (fun t => i t ≫ (b t).left) z) : HolAt (fun t => i t ≫ (lift (a t) (b t)).left) z := by sorry
