-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotKer_ker_sq_le_ker
-- name    : GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:48.358801+00:00
-- url     : https://prove2.me/theorems/27b120c3-4b44-4887-a955-90c35863380e
-- title:
--   Cot Ker: ker sq le ker
-- statement:
--   The Cot Ker construction uses the ker sq le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IdealSquareLeKernelOfSquareZeroMap.lean#L68-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IdealSquareLeKernelOfSquareZeroMap.lean#L68-L84

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdealSquareLeKernelOfSquareZeroMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotKer

theorem GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker : ∀ (R Q B : Type) [CommRing R] [CommRing Q] [CommRing B] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ U), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → e.ker ^ 2 ≤ y.ker := by sorry
