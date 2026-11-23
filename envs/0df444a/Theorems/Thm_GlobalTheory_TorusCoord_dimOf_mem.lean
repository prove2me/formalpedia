-- Prove2me | Theorems.Thm_GlobalTheory_TorusCoord_dimOf_mem
-- name    : GlobalTheory.TorusCoord.dimOf_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:11.697842+00:00
-- url     : https://prove2.me/theorems/5dec74df-eaaf-40d4-a0de-070e509c5e1f
-- title:
--   Torus Coord: dim Of mem
-- statement:
--   The Torus Coord construction uses the dim Of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L47-L48

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

theorem GlobalTheory.TorusCoord.dimOf_mem (X : Data E r) {σ : E →+* ℂ} (h : σ ∈ X.Ψ) : dimOf X σ = X.p0 := by sorry
