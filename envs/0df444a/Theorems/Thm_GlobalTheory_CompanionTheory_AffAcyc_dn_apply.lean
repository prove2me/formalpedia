-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_apply
-- name    : GlobalTheory.CompanionTheory.AffAcyc.dn_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:25:46.228134+00:00
-- url     : https://prove2.me/theorems/51567306-f002-4463-a6e9-09ff7876aa7f
-- title:
--   Aff Acyc: dn apply
-- statement:
--   The Aff Acyc construction uses the dn apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L17-L21

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

theorem GlobalTheory.CompanionTheory.AffAcyc.dn_apply (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (z : Cn F n) (c : Fin (n + 2) ⥤ C) :
    dn F n z c = ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) •
      mp F (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))) (z (face i c)) := by sorry
