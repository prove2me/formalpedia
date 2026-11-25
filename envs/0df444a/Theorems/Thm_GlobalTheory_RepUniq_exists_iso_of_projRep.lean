-- Prove2me | Theorems.Thm_GlobalTheory_RepUniq_exists_iso_of_projRep
-- name    : GlobalTheory.RepUniq.exists_iso_of_projRep
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:49.410557+00:00
-- url     : https://prove2.me/theorems/0ce4fd61-dfa8-5010-878b-ce6c481abde5
-- title:
--   Rep Uniq: exists iso of proj Rep
-- statement:
--   The Rep Uniq construction uses the exists iso of proj Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsoOfProjectiveCoordinateRepresentation.lean#L366-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsoOfProjectiveCoordinateRepresentation.lean#L366-L379

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsoOfProjectiveCoordinateRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.RepUniq
open TopologicalSpace GlobalTheory.Cartier GlobalTheory.ProjSpace
variable {σ : Type} {T T' X X' X'' : Scheme.{0}}
variable {M : LB X} {th : σ → M.Sec} {M' : LB X'} {th' : σ → M'.Sec} {M'' : LB X''} {th'' : σ → M''.Sec}
  {x : T ⟶ X} {x' : T ⟶ X'} {x'' : T ⟶ X''}

theorem GlobalTheory.RepUniq.exists_iso_of_projRep : ∀ (R σ : Type) [CommRing R] (I I' : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R) (M : LB Z) (M' : LB Z') (th : σ → M.Sec) (th' : σ → M'.Sec), ProjRep I s M th → ProjRep I' s' M' th' → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (v : σ → R'), Ideal.span (Set.range v) = ⊤ → ((∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) ↔ ∀ F ∈ I', MvPolynomial.eval₂ β v F = 0)) → ∃ e : Z ≅ Z', e.hom ≫ s' = s ∧ LBIso M (M'.pull e.hom) ∧ ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Z) (v : σ → R'), SecCoord M th x v ↔ SecCoord M' th' (x ≫ e.hom) v := by sorry
