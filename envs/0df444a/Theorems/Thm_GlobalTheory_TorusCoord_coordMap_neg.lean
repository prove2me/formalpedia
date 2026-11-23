-- Prove2me | Theorems.Thm_GlobalTheory_TorusCoord_coordMap_neg
-- name    : GlobalTheory.TorusCoord.coordMap_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:51.025335+00:00
-- url     : https://prove2.me/theorems/5a60f8c2-e167-487c-8fef-051fc0f21821
-- title:
--   Torus Coord: coord Map neg
-- statement:
--   The Torus Coord construction uses the coord Map neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L148-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L148-L157

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

theorem GlobalTheory.TorusCoord.coordMap_neg (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
    (a : Fin (dimOf X (ComplexEmbedding.conjugate τ.1))) :
    coordMap X e y ⟨ComplexEmbedding.conjugate τ.1, a⟩ =
      - conj (pr X e y τ ⟨X.p0 + a.1, lt_neg X ((X.cmType _).mp τ.2) a⟩) := by sorry
