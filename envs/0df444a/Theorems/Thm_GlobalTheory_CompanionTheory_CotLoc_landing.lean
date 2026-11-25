-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_landing
-- name    : GlobalTheory.CompanionTheory.CotLoc.landing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:37.250075+00:00
-- url     : https://prove2.me/theorems/78d1a64a-2993-5915-9491-95961164aca6
-- title:
--   Cot Loc: landing
-- statement:
--   The Cot Loc construction uses the landing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L17-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L17-L40

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc

theorem GlobalTheory.CompanionTheory.CotLoc.landing {X : Scheme.{0}} {A Q R' : Type} [CommRing A] [CommRing Q] [CommRing R']
    (j : Sp A ⟶ X) [IsOpenImmersion j] (ε : A →+* R') (q : Q →+* R')
    (hq : Function.Surjective q) (hnil : ∀ x, q x = 0 → IsNilpotent x)
    (y : Sp Q ⟶ X) (hy : spMap q ≫ y = spMap ε ≫ j) :
    ∃ ψ : A →+* Q, y = spMap ψ ≫ j := by sorry
