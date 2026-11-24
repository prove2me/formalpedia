-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_res_bij
-- name    : GlobalTheory.CompanionTheory.AffAcyc.res_bij
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:25:49.71772+00:00
-- url     : https://prove2.me/theorems/1fc9fa8e-a2a3-4618-a187-57cab62c47ec
-- title:
--   Aff Acyc: res bij
-- statement:
--   The Aff Acyc construction uses the res bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L266-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L266-L272

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

theorem GlobalTheory.CompanionTheory.AffAcyc.res_bij (s : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (e : U = V) :
    Function.Bijective (Sec.res s h) := by sorry
