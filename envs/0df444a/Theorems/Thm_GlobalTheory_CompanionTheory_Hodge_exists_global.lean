-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_exists_global
-- name    : GlobalTheory.CompanionTheory.Hodge.exists_global
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:25:13.494896+00:00
-- url     : https://prove2.me/theorems/5ef5133c-da5d-470d-823d-b3ee2ed5ec34
-- title:
--   Hodge: exists global
-- statement:
--   The Hodge construction uses the exists global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SteinOfBijective.lean#L36-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SteinOfBijective.lean#L36-L54

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

theorem GlobalTheory.CompanionTheory.Hodge.exists_global (g : ∀ U : X.affineOpens, Γ(X, U.1))
    (hg : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1), X.presheaf.map (homOfLE h).op (g U) = g V) :
    ∃ t : Γ(X, ⊤), ∀ U : X.affineOpens,
      X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op t = g U := by sorry
