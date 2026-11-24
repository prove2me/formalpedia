-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotKer_mul_eq_zero_affine
-- name    : GlobalTheory.CompanionTheory.CotKer.mul_eq_zero_affine
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:02.830798+00:00
-- url     : https://prove2.me/theorems/0d211551-c6f7-4251-9184-4fd762018cbd
-- title:
--   Cot Ker: mul eq zero affine
-- statement:
--   The Cot Ker construction uses the mul eq zero affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IdealSquareLeKernelOfSquareZeroMap.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IdealSquareLeKernelOfSquareZeroMap.lean#L31-L41

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

theorem GlobalTheory.CompanionTheory.CotKer.mul_eq_zero_affine {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (W : (Sp Q).affineOpens) (a b : Γ(Sp Q, W.1))
    (ha : ((spMap q).app W.1).hom a = 0) (hb : ((spMap q).app W.1).hom b = 0) : a * b = 0 := by sorry
