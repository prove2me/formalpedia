-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_isDerivAt_lift
-- name    : GlobalTheory.HolHom.isDerivAt_lift
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:36:12.621247+00:00
-- url     : https://prove2.me/theorems/2fdbf610-0020-4b03-a958-6cf3d4d7e056
-- title:
--   Hol Hom: is Deriv At lift
-- statement:
--   The Hol Hom construction uses the is Deriv At lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L389-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L389-L405

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
omit [GrpObj G]

theorem GlobalTheory.HolHom.isDerivAt_lift {G' : Over S} {a : V → (Over.mk y ⟶ G)} {b : V → (Over.mk y ⟶ G')} {z w : V}
    (ha : HolAt (fun t => (a t).left) z) (hb : HolAt (fun t => (b t).left) z) {v : epsPt y ⟶ G} {v' : epsPt y ⟶ G'}
    (hv : IsDerivAt (fun t => (a t).left) z w v.left) (hv' : IsDerivAt (fun t => (b t).left) z w v'.left) :
    IsDerivAt (fun t => (lift (a t) (b t)).left) z w (lift v v').left := by sorry
