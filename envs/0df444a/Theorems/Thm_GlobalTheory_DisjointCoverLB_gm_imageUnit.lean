-- Prove2me | Theorems.Thm_GlobalTheory_DisjointCoverLB_gm_imageUnit
-- name    : GlobalTheory.DisjointCoverLB.gm_imageUnit
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:51:11.680995+00:00
-- url     : https://prove2.me/theorems/89fb0a9d-8ef0-4cc4-8966-aa1fb03fb1ad
-- title:
--   Disjoint Cover LB: gm image Unit
-- statement:
--   The Disjoint Cover LB construction uses the gm image Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LbIsoOfDisjointCover.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LbIsoOfDisjointCover.lean#L12-L22

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

theorem GlobalTheory.DisjointCoverLB.gm_imageUnit {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsOpenImmersion ι] (V : Z.Opens) (v : Γ(Z, V)ˣ) (z : Z)
    (hz : z ∈ V) :
    gm ι z (ι ''ᵁ V) (GlobalTheory.ExtendLineBundle.imageUnit ι V v) = gm (𝟙 Z) z V v := by sorry
