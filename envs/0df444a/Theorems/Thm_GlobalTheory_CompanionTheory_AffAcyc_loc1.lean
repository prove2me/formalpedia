-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_loc1
-- name    : GlobalTheory.CompanionTheory.AffAcyc.loc1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:25:15.116275+00:00
-- url     : https://prove2.me/theorems/fb1ea41a-4592-4093-b921-79a538c5b73e
-- title:
--   Aff Acyc: loc1
-- statement:
--   The Aff Acyc construction uses the loc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L305-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L305-L311

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

theorem GlobalTheory.CompanionTheory.AffAcyc.loc1 (f : Γ(X, W.1)) (T : Pᵒᵖ) (y' : (FF s (uf s W u hle f)).obj T) :
    ∃ (N : ℕ) (y : (FF s u).obj T), rho s W u hle f T y =
      rho s W u hle f T (gF s W u hle f T) ^ N * y' := by sorry
