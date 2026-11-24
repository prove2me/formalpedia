-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_isDerivAt_mul
-- name    : GlobalTheory.HolHom.isDerivAt_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:36:16.56229+00:00
-- url     : https://prove2.me/theorems/72a1a9df-27af-4acc-8d83-c32f3a49b09b
-- title:
--   Hol Hom: is Deriv At mul
-- statement:
--   The Hol Hom construction uses the is Deriv At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L407-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L407-L411

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
variable {G : Over S} [GrpObj G]
variable {y : Sp ℂ ⟶ S}

theorem GlobalTheory.HolHom.isDerivAt_mul {a b : V → (Over.mk y ⟶ G)} {z w : V}
    (ha : HolAt (fun t => (a t).left) z) (hb : HolAt (fun t => (b t).left) z) {v v' : epsPt y ⟶ G}
    (hv : IsDerivAt (fun t => (a t).left) z w v.left) (hv' : IsDerivAt (fun t => (b t).left) z w v'.left) :
    IsDerivAt (fun t => (a t * b t).left) z w (v * v').left := by sorry
