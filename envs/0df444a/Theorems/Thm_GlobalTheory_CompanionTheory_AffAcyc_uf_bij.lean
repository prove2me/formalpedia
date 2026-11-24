-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_uf_bij
-- name    : GlobalTheory.CompanionTheory.AffAcyc.uf_bij
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:26:27.462769+00:00
-- url     : https://prove2.me/theorems/d20d5f94-5929-4a57-8569-ada8c240d0ce
-- title:
--   Aff Acyc: uf bij
-- statement:
--   The Aff Acyc construction uses the uf bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L320-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L320-L328

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
variable {R : Type} [CommRing R] {X : Scheme.{0}} {P : Type} [SemilatticeInf P]
variable (s : X ⟶ Sp R) (W : X.affineOpens) (u : P →o X.affineOpens) (hle : ∀ a, (u a).1 ≤ W.1)

theorem GlobalTheory.CompanionTheory.AffAcyc.uf_bij (hinf : ∀ a b, (u (a ⊓ b)).1 = (u a).1 ⊓ (u b).1) (f : Γ(X, W.1)) (a₀ : P)
    (hf : X.basicOpen f ≤ (u a₀).1) (T : Pᵒᵖ) :
    Function.Bijective (mp (FF s (uf s W u hle f)) ((th a₀).app T)) := by sorry
