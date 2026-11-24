-- Prove2me | Theorems.Thm_GlobalTheory_isGrpPullback_of_fpqc
-- name    : GlobalTheory.isGrpPullback_of_fpqc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:43:19.329922+00:00
-- url     : https://prove2.me/theorems/4625110c-87d7-40e6-a9b5-52ca33dbe676
-- title:
--   Global Theory: is Grp Pullback of fpqc
-- statement:
--   The Global Theory construction uses the is Grp Pullback of fpqc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsPullbackOfFpqcLeft.lean#L14-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsPullbackOfFpqcLeft.lean#L14-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsPullbackOfFpqcLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.isGrpPullback_of_fpqc (S S' S'' : Scheme.{0}) (a : S' ⟶ S) (π : S'' ⟶ S') (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (G'' : Over S'') [GrpObj G''] (φ : G''.left ⟶ G'.left) (ψ : G'.left ⟶ G.left)
    (hf : Flat π) (hs : Surjective π) (hq : QuasiCompact π) (h₁ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G' π φ)
    (h₂ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G (π ≫ a) (φ ≫ ψ)) (w : ψ ≫ G.hom = G'.hom ≫ a) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G a ψ := by sorry
