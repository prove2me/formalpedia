-- Prove2me | Theorems.Thm_GlobalTheory_StalkLimit_exists_spread
-- name    : GlobalTheory.StalkLimit.exists_spread
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:16:31.573865+00:00
-- url     : https://prove2.me/theorems/0e611fd4-1cb0-40ed-a606-f4bb9b2e058e
-- title:
--   Stalk Limit: exists spread
-- statement:
--   The Stalk Limit construction uses the exists spread property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L152-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L152-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.StalkLimit
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
variable {S X : Scheme.{u}} (x : S) (p : X ⟶ S)
variable {x p} {X' : Scheme.{u}} {φ : X' ⟶ X} {p' : X' ⟶ Spec (S.presheaf.stalk x)}

theorem GlobalTheory.StalkLimit.exists_spread [QuasiCompact p] [QuasiSeparated p] (h : IsPullback φ p' p (S.fromSpecStalk x))
    {Y : Scheme.{u}} (q : Y ⟶ S) [LocallyOfFinitePresentation q] (a : X' ⟶ Y) (ha : a ≫ q = φ ≫ p) :
    ∃ (V : S.Opens) (_ : x ∈ V) (_ : IsAffineOpen V) (w : X' ⟶ pullback p V.ι) (g : pullback p V.ι ⟶ Y),
      w ≫ pullback.fst p V.ι = φ ∧ w ≫ g = a ∧ g ≫ q = pullback.fst p V.ι ≫ p := by sorry
