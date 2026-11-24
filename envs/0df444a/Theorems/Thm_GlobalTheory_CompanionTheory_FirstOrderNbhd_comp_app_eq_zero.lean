-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FirstOrderNbhd_comp_app_eq_zero
-- name    : GlobalTheory.CompanionTheory.FirstOrderNbhd.comp_app_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:21:51.433558+00:00
-- url     : https://prove2.me/theorems/d0463a14-b4fa-4f86-9091-86c22ad7a82b
-- title:
--   First Order Nbhd: comp app eq zero
-- statement:
--   The First Order Nbhd construction uses the comp app eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquareZeroNeighbourhoodProductZero.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquareZeroNeighbourhoodProductZero.lean#L8-L20

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodProductZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FirstOrderNbhd

theorem GlobalTheory.CompanionTheory.FirstOrderNbhd.comp_app_eq_zero {E T U : Scheme.{0}} (c : E ⟶ U) (i' : T ⟶ E) (W : U.Opens)
    (a' : Γ(U, W)) (a : Γ(E, ⊤)) (h : c.app W a' = E.presheaf.map (homOfLE le_top).op a)
    (ha : i'.appTop a = 0) : (i' ≫ c).app W a' = 0 := by sorry
