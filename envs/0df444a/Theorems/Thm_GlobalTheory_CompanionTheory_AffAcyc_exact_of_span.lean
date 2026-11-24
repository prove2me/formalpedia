-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_exact_of_span
-- name    : GlobalTheory.CompanionTheory.AffAcyc.exact_of_span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:25:13.235795+00:00
-- url     : https://prove2.me/theorems/efd1b9dd-e275-489f-a206-eb26ce2e7d19
-- title:
--   Aff Acyc: exact of span
-- statement:
--   The Aff Acyc construction uses the exact of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L221-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L221-L253

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

theorem GlobalTheory.CompanionTheory.AffAcyc.exact_of_span {B : Type} [CommRing B] (F : C ⥤ CommAlgCat.{0} R) (io' : ∀ T, B →+* F.obj T)
    (hio : ∀ (T T' : C) (φ : T ⟶ T') (b : B), mp F φ (io' T b) = io' T' b) (S : Set B)
    (hS : Ideal.span S = ⊤) (n : ℕ) (z : Cn F (n + 1))
    (h : ∀ f ∈ S, ∃ (N : ℕ) (y : Cn F n), dn F n y = sc F (fun T ↦ io' T f ^ N) (n + 1) z) :
    ∃ y, dn F n y = z := by sorry
