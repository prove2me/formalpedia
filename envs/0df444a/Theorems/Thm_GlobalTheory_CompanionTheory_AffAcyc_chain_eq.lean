-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_chain_eq
-- name    : GlobalTheory.CompanionTheory.AffAcyc.chain_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:25:41.492828+00:00
-- url     : https://prove2.me/theorems/cfdc51bd-a74c-4a0d-83ef-4acb3e852795
-- title:
--   Aff Acyc: chain eq
-- statement:
--   The Aff Acyc construction uses the chain eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L356-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean#L356-L358

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

theorem GlobalTheory.CompanionTheory.AffAcyc.chain_eq (c : Fin 1 ⥤ Pᵒᵖ) : c = (Functor.const (Fin 1)).obj (c.obj 0) := by sorry
