-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FirstOrderNbhd_exists_mem_ideal_of_lift
-- name    : GlobalTheory.CompanionTheory.FirstOrderNbhd.exists_mem_ideal_of_lift
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:34.89837+00:00
-- url     : https://prove2.me/theorems/3b2c1a59-b9de-4d9e-8606-5efb5537992e
-- title:
--   First Order Nbhd: exists mem ideal of lift
-- statement:
--   The First Order Nbhd construction uses the exists mem ideal of lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquareZeroNeighbourhoodProductZero.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquareZeroNeighbourhoodProductZero.lean#L22-L33

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

theorem GlobalTheory.CompanionTheory.FirstOrderNbhd.exists_mem_ideal_of_lift {T U : Scheme.{0}} (e : T ⟶ U) [QuasiCompact e]
    (i' : T ⟶ (e.ker ^ 2).subscheme) (hi : i' ≫ (e.ker ^ 2).subschemeι = e)
    (W : U.affineOpens) (a : Γ((e.ker ^ 2).subscheme, ⊤)) (ha : i'.appTop a = 0) :
    ∃ a' ∈ e.ker.ideal W, (e.ker ^ 2).subschemeι.app W a' =
      (e.ker ^ 2).subscheme.presheaf.map (homOfLE le_top).op a := by sorry
