-- Prove2me | Theorems.Thm_GlobalTheory_TorusCoord_dimOf_not_mem
-- name    : GlobalTheory.TorusCoord.dimOf_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:58.460147+00:00
-- url     : https://prove2.me/theorems/be00aeb9-5ae5-4d91-b9cf-06a34e427500
-- title:
--   Torus Coord: dim Of not mem
-- statement:
--   The Torus Coord construction uses the dim Of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L50-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.TorusCoord
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.TorusCoord.dimOf_not_mem (X : Data E r) {σ : E →+* ℂ} (h : σ ∉ X.Ψ) : dimOf X σ = r - X.p0 := by sorry
