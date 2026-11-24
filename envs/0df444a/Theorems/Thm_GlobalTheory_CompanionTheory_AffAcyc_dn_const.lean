-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_const
-- name    : GlobalTheory.CompanionTheory.AffAcyc.dn_const
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:25:20.097596+00:00
-- url     : https://prove2.me/theorems/c4ddd592-f89d-4726-a0e3-aa0f5d794529
-- title:
--   Aff Acyc: dn const
-- statement:
--   The Aff Acyc construction uses the dn const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L111-L117

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

theorem GlobalTheory.CompanionTheory.AffAcyc.dn_const (n : ℕ) (z : Cn F n) :
    dn F n z ((Functor.const (Fin (n + 2))).obj (op a₀)) =
      (∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ)) • z ((Functor.const (Fin (n + 1))).obj (op a₀)) := by sorry
