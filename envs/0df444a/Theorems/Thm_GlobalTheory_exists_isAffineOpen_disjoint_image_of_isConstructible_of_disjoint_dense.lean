-- Prove2me | Theorems.Thm_GlobalTheory_exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense
-- name    : GlobalTheory.exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:30.165307+00:00
-- url     : https://prove2.me/theorems/36c987e9-c38b-4a05-910c-55da810aff81
-- title:
--   Global Theory: exists is Affine Open disjoint image of is Constructible of disjoint dense
-- statement:
--   The Global Theory construction uses the exists is Affine Open disjoint image of is Constructible of disjoint dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsAffineOpenDisjointImageOfIsConstructible.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsAffineOpenDisjointImageOfIsConstructible.lean#L22-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsAffineOpenDisjointImageOfIsConstructible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory

theorem GlobalTheory.exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense :
    ∀ (X S : Scheme.{0}) [IsIntegral S] [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (C : Set X) (Sg : Set S), Topology.IsConstructible C → Dense Sg → Disjoint (f '' C) Sg → ∃ V : S.Opens, (V : Set S).Nonempty ∧ IsAffineOpen V ∧ Disjoint (f '' C) V := by sorry
