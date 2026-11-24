-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_common_exp
-- name    : GlobalTheory.CompanionTheory.AffAcyc.common_exp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:26:30.458152+00:00
-- url     : https://prove2.me/theorems/b1223ca6-9f9b-4997-bbe1-5941c67b3bf2
-- title:
--   Aff Acyc: common exp
-- statement:
--   The Aff Acyc construction uses the common exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L159-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L159-L163

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

theorem GlobalTheory.CompanionTheory.AffAcyc.common_exp {J : Type} [Finite J] (p : J → ℕ → Prop) (hp : ∀ i, ∃ N, ∀ M, N ≤ M → p i M) :
    ∃ N, ∀ i, p i N := by sorry
