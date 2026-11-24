-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_loc2
-- name    : GlobalTheory.CompanionTheory.AffAcyc.loc2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:25:21.543355+00:00
-- url     : https://prove2.me/theorems/a79f8b8d-ef44-4998-8dfb-76aed1733288
-- title:
--   Aff Acyc: loc2
-- statement:
--   The Aff Acyc construction uses the loc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L313-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L313-L318

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

theorem GlobalTheory.CompanionTheory.AffAcyc.loc2 (f : Γ(X, W.1)) (T : Pᵒᵖ) (y : (FF s u).obj T) (hy : rho s W u hle f T y = 0) :
    ∃ N : ℕ, gF s W u hle f T ^ N * y = 0 := by sorry
