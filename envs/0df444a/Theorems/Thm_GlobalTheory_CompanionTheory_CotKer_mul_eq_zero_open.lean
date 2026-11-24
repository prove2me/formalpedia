-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotKer_mul_eq_zero_open
-- name    : GlobalTheory.CompanionTheory.CotKer.mul_eq_zero_open
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:51.005808+00:00
-- url     : https://prove2.me/theorems/7720a225-3ed4-4d0a-a04f-bad17f100ebf
-- title:
--   Cot Ker: mul eq zero open
-- statement:
--   The Cot Ker construction uses the mul eq zero open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IdealSquareLeKernelOfSquareZeroMap.lean#L43-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IdealSquareLeKernelOfSquareZeroMap.lean#L43-L62

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

theorem GlobalTheory.CompanionTheory.CotKer.mul_eq_zero_open {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (O : (Sp Q).Opens) (a b : Γ(Sp Q, O))
    (ha : ((spMap q).app O).hom a = 0) (hb : ((spMap q).app O).hom b = 0) : a * b = 0 := by sorry
