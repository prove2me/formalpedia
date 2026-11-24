-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_over
-- name    : GlobalTheory.HolHom.IsDerivAt.over
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:45:27.034785+00:00
-- url     : https://prove2.me/theorems/9fd35ee1-9636-4089-8a31-3e98fe3ab2c9
-- title:
--   Is Deriv At: over
-- statement:
--   The Is Deriv At construction uses the over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L381-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L381-L385

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

theorem GlobalTheory.HolHom.IsDerivAt.over {a : V → (Over.mk y ⟶ G)} {z w : V} {v : Sp (DualNumber ℂ) ⟶ G.left}
    (h : IsDerivAt (fun t => (a t).left) z w v) : v ≫ G.hom = (epsPt y).hom := by sorry
