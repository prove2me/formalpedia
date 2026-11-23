-- Prove2me | Theorems.Thm_GlobalTheory_TorusCoord_sum_emb_split
-- name    : GlobalTheory.TorusCoord.sum_emb_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:11.944141+00:00
-- url     : https://prove2.me/theorems/325166cc-9ad9-43c2-aa72-04b97641548a
-- title:
--   Torus Coord: sum emb split
-- statement:
--   The Torus Coord construction uses the sum emb split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L19-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L19-L41

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
open NumberField
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.TorusCoord.sum_emb_split {M : Type} [AddCommMonoid M] (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (F : (E →+* ℂ) → M) :
    ∑ σ, F σ = ∑ τ : X.Ψ, (F τ.1 + F (ComplexEmbedding.conjugate τ.1)) := by sorry
