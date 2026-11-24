-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_z_cocycle
-- name    : GlobalTheory.CompanionTheory.AffAcyc.z_cocycle
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:25:58.928325+00:00
-- url     : https://prove2.me/theorems/4be9f6f5-e8ca-4845-9ac1-79aa361af2b6
-- title:
--   Aff Acyc: z cocycle
-- statement:
--   The Aff Acyc construction uses the z cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L364-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L364-L377

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
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)

theorem GlobalTheory.CompanionTheory.AffAcyc.z_cocycle (z : Cn F 0) (hz : dn F 0 z = 0) {T T' : Pᵒᵖ} (φ : T ⟶ T') :
    mp F φ (z ((Functor.const (Fin 1)).obj T)) = z ((Functor.const (Fin 1)).obj T') := by sorry
