-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_rT_sR
-- name    : GlobalTheory.CompanionTheory.HypWedge.rT_sR
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:25:44.24129+00:00
-- url     : https://prove2.me/theorems/254a60ef-5bf3-5a4e-8311-430bbb97857e
-- title:
--   Hyp Wedge: r T s R
-- statement:
--   The Hyp Wedge construction uses the r T s R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L186-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L186-L191

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.HypWedge.rT_sR (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) (hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v) (u : H1 F ⊗[R] Glob1 F) :
    LinearMap.rTensor (Glob1 F) (H1.mk F) (sR τ u) = u := by sorry
