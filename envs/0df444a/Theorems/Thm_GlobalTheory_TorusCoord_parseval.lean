-- Prove2me | Theorems.Thm_GlobalTheory_TorusCoord_parseval
-- name    : GlobalTheory.TorusCoord.parseval
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:20.14783+00:00
-- url     : https://prove2.me/theorems/8097142c-db47-486c-b16b-a7b81d3186a2
-- title:
--   Torus Coord: parseval
-- statement:
--   The Torus Coord construction uses the parseval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L193-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L193-L202

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

theorem GlobalTheory.TorusCoord.parseval (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
    (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) =
      if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u v = ∑ a : Fin r, ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) *
      (hermC τ.1 X.Gm u (e a) * conj (hermC τ.1 X.Gm v (e a))) := by sorry
