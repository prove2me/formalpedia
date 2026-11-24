-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_isHolTo_mul
-- name    : GlobalTheory.HolHom.isHolTo_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:38:02.526494+00:00
-- url     : https://prove2.me/theorems/412d80b3-7b8c-44c3-be3d-9eb3ad84fb55
-- title:
--   Hol Hom: is Hol To mul
-- statement:
--   The Hol Hom construction uses the is Hol To mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L365-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L365-L371

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

theorem GlobalTheory.HolHom.isHolTo_mul {B : Set V} {y : V → (Sp ℂ ⟶ S)} {a b : ∀ t, Over.mk (y t) ⟶ G}
    (ha : IsHolTo B (fun t => (a t).left)) (hb : IsHolTo B (fun t => (b t).left)) :
    IsHolTo B (fun t => (a t * b t).left) := by sorry
