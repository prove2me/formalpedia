-- Prove2me | Theorems.Thm_GlobalTheory_DisjointCoverLB_units_eq_of_gm
-- name    : GlobalTheory.DisjointCoverLB.units_eq_of_gm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:51:03.066817+00:00
-- url     : https://prove2.me/theorems/06e25197-84cb-4cda-a23b-94e6d4c7c345
-- title:
--   Disjoint Cover LB: units eq of gm
-- statement:
--   The Disjoint Cover LB construction uses the units eq of gm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LbIsoOfDisjointCover.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LbIsoOfDisjointCover.lean#L24-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LbIsoOfDisjointCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.DisjointCoverLB

theorem GlobalTheory.DisjointCoverLB.units_eq_of_gm {X : Scheme.{0}} {V : X.Opens} {a b : Γ(X, V)ˣ}
    (h : ∀ x ∈ V, ∃ (Z : Scheme.{0}) (ι : Z ⟶ X) (_ : IsOpenImmersion ι) (z : Z), ι z = x ∧ gm ι z V a = gm ι z V b) :
    a = b := by sorry
