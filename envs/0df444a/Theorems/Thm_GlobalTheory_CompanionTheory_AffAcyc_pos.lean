-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_pos
-- name    : GlobalTheory.CompanionTheory.AffAcyc.pos
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:25:37.626992+00:00
-- url     : https://prove2.me/theorems/8d575c9a-7093-4b95-97a0-11dfd7cc56fe
-- title:
--   Aff Acyc: pos
-- statement:
--   The Aff Acyc construction uses the pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L332-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L332-L348

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
include hle

theorem GlobalTheory.CompanionTheory.AffAcyc.pos [Finite P] (hC : CxSt) (hH : HtpySt) (hinf : ∀ a b, (u (a ⊓ b)).1 = (u a).1 ⊓ (u b).1)
    (hcov : ⨆ a, (u a).1 = W.1) (n : ℕ) (z : Cn (FF s u) (n + 1))
    (hz : dn (FF s u) (n + 1) z = 0) : ∃ y, dn (FF s u) n y = z := by sorry
