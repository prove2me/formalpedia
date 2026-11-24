-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_isHolTo_inv
-- name    : GlobalTheory.HolHom.isHolTo_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:38:41.14681+00:00
-- url     : https://prove2.me/theorems/81b254f0-b467-4d13-91c1-2766e55e9fa7
-- title:
--   Hol Hom: is Hol To inv
-- statement:
--   The Hol Hom construction uses the is Hol To inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L373-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L373-L375

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

theorem GlobalTheory.HolHom.isHolTo_inv {B : Set V} {y : V → (Sp ℂ ⟶ S)} {a : ∀ t, Over.mk (y t) ⟶ G}
    (ha : IsHolTo B (fun t => (a t).left)) : IsHolTo B (fun t => ((a t)⁻¹).left) := by sorry
