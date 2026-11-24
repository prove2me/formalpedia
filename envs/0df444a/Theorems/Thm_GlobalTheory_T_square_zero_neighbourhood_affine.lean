-- Prove2me | Theorems.Thm_GlobalTheory_T_square_zero_neighbourhood_affine
-- name    : GlobalTheory.T.square_zero_neighbourhood_affine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:19.413804+00:00
-- url     : https://prove2.me/theorems/d2bcdbc8-5f20-401b-a702-2f5b74b7f8b8
-- title:
--   T: square zero neighbourhood affine
-- statement:
--   The T construction uses the square zero neighbourhood affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquareZeroNeighbourhoodAffineStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquareZeroNeighbourhoodAffineStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodAffine
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodAffineStatement
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

theorem GlobalTheory.T.square_zero_neighbourhood_affine : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (t : U ⟶ Sp R) (e : Sp R ⟶ U) [IsClosedImmersion e], e ≫ t = 𝟙 _ → IsAffine (e.ker ^ 2).subscheme := by sorry
