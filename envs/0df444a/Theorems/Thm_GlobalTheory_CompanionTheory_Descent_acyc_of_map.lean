-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_of_map
-- name    : GlobalTheory.CompanionTheory.Descent.acyc_of_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:26:24.610252+00:00
-- url     : https://prove2.me/theorems/9bcffd72-d8e6-4d78-8099-4b240a1f4fd1
-- title:
--   Descent: acyc of map
-- statement:
--   The Descent construction uses the acyc of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L120-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L120-L140

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Descent
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]

theorem GlobalTheory.CompanionTheory.Descent.acyc_of_map (hCx : CxSt) (hA : AffAcycSt) (f : D ⥤ AffOp X) (f' : E ⥤ AffOp X) (σ : E ⥤ D) (h)
    (W : X.affineOpens) (hle hle')
    (Q1 : ∀ x, dn (f ⋙ OAff s) 0 x = 0 → pulln (rm s f f' σ h) 0 x = 0 → x = 0)
    (Q2 : ∀ n x, dn (f ⋙ OAff s) (n + 1) x = 0 →
      (∃ y, dn (f' ⋙ OAff s) n y = pulln (rm s f f' σ h) (n + 1) x) → ∃ y, dn (f ⋙ OAff s) n y = x)
    (A : Acyc s f' W.1 hle') : Acyc s f W.1 hle := by sorry
