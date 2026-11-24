-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_sc
-- name    : GlobalTheory.CompanionTheory.AffAcyc.dn_sc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:49.200401+00:00
-- url     : https://prove2.me/theorems/3e26a1a0-cda6-428e-a549-2ba994b869b8
-- title:
--   Aff Acyc: dn sc
-- statement:
--   The Aff Acyc construction uses the dn sc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L26-L34

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

theorem GlobalTheory.CompanionTheory.AffAcyc.dn_sc (F : C ⥤ CommAlgCat.{0} R) (g : ∀ T, F.obj T)
    (hg : ∀ (T T' : C) (φ : T ⟶ T'), mp F φ (g T) = g T') (n : ℕ) (z : Cn F n) :
    dn F n (sc F g n z) = sc F g (n + 1) (dn F n z) := by sorry
