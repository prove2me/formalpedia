-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_E
-- name    : GlobalTheory.CompanionTheory.AffAcyc.dn_E
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:25:07.89091+00:00
-- url     : https://prove2.me/theorems/7ac19b0a-3832-4e59-ac4d-7cf239666bd8
-- title:
--   Aff Acyc: dn E
-- statement:
--   The Aff Acyc construction uses the dn E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L100-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L100-L109

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
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
variable (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (a₀ : P)
  (hb : ∀ T : Pᵒᵖ, Function.Bijective (mp F ((th a₀).app T)))

theorem GlobalTheory.CompanionTheory.AffAcyc.dn_E (n : ℕ) (t : F.obj (op a₀)) (c : Fin (n + 2) ⥤ Pᵒᵖ) :
    dn F n (E F a₀ hb n t) c = (∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ)) • E F a₀ hb (n + 1) t c := by sorry
