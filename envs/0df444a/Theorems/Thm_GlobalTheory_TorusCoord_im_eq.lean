-- Prove2me | Theorems.Thm_GlobalTheory_TorusCoord_im_eq
-- name    : GlobalTheory.TorusCoord.im_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:42:46.216144+00:00
-- url     : https://prove2.me/theorems/3e167809-008a-59c8-87bb-8812741ae66f
-- title:
--   Torus Coord: im eq
-- statement:
--   The Torus Coord construction uses the im eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L204-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean#L204-L242

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

theorem GlobalTheory.TorusCoord.im_eq (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ))
    (he : ∀ τ a b, hermC τ.1 X.Gm (e τ a) (e τ b) =
      if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) (y y' : X.Ψ → Fin r → ℂ) :
    (Hf (coordMap X e y) (coordMap X e y')).im =
      ∑ τ : X.Ψ, X.c τ * (hermC τ.1 X.Gm (y τ) (y' τ)).im := by sorry
