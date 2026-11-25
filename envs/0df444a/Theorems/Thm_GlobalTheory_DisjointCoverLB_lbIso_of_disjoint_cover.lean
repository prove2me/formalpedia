-- Prove2me | Theorems.Thm_GlobalTheory_DisjointCoverLB_lbIso_of_disjoint_cover
-- name    : GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:51:09.284672+00:00
-- url     : https://prove2.me/theorems/a68e8f1c-3186-458c-850f-966e417fcae0
-- title:
--   Disjoint Cover LB: lb Iso of disjoint cover
-- statement:
--   The Disjoint Cover LB construction uses the lb Iso of disjoint cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LbIsoOfDisjointCover.lean#L40-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LbIsoOfDisjointCover.lean#L40-L89

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

theorem GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover : ∀ (Y : Scheme.{0}) (A : Type) (W : A → Y.Opens), (∀ a b y, y ∈ W a → y ∈ W b → a = b) →
    (∀ y, ∃ a, y ∈ W a) → ∀ (P Q : LB Y), P.IsLB → Q.IsLB → (∀ a, LBIso (P.pull (W a).ι) (Q.pull (W a).ι)) →
    LBIso P Q := by sorry
