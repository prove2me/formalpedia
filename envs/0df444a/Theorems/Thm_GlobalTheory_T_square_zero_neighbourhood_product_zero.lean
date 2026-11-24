-- Prove2me | Theorems.Thm_GlobalTheory_T_square_zero_neighbourhood_product_zero
-- name    : GlobalTheory.T.square_zero_neighbourhood_product_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:32.669461+00:00
-- url     : https://prove2.me/theorems/99cfb0ce-25b7-4552-924d-d471885620fe
-- title:
--   T: square zero neighbourhood product zero
-- statement:
--   The T construction uses the square zero neighbourhood product zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquareZeroNeighbourhoodProductZeroStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquareZeroNeighbourhoodProductZeroStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodProductZero
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodProductZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.square_zero_neighbourhood_product_zero : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (i' : Sp R ⟶ (e.ker ^ 2).subscheme), i' ≫ (e.ker ^ 2).subschemeι = e → ∀ a b : Γ((e.ker ^ 2).subscheme, ⊤), i'.appTop a = 0 → i'.appTop b = 0 → a * b = 0 := by sorry
