-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_rho_nat
-- name    : GlobalTheory.CompanionTheory.AffAcyc.rho_nat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:25:18.667988+00:00
-- url     : https://prove2.me/theorems/b47a29f4-e793-4ae5-8fa3-20b6b3477ddd
-- title:
--   Aff Acyc: rho nat
-- statement:
--   The Aff Acyc construction uses the rho nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L295-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L295-L297

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

theorem GlobalTheory.CompanionTheory.AffAcyc.rho_nat (f : Γ(X, W.1)) {T T' : Pᵒᵖ} (φ : T ⟶ T') (b : (FF s u).obj T) :
    rho s W u hle f T' (mp (FF s u) φ b) = mp (FF s (uf s W u hle f)) φ (rho s W u hle f T b) := by sorry
