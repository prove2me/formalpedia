-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_eq_of_res_affine
-- name    : GlobalTheory.CompanionTheory.Hodge.eq_of_res_affine
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:35:21.338421+00:00
-- url     : https://prove2.me/theorems/9f43849d-89e8-442f-b200-2feba397a52c
-- title:
--   Hodge: eq of res affine
-- statement:
--   The Hodge construction uses the eq of res affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SteinOfBijective.lean#L23-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SteinOfBijective.lean#L23-L34

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SteinOfBijective
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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge
variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem GlobalTheory.CompanionTheory.Hodge.eq_of_res_affine (W : X.Opens) (a b : Γ(X, W))
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W),
      X.presheaf.map (homOfLE hV).op a = X.presheaf.map (homOfLE hV).op b) : a = b := by sorry
