-- Prove2me | Theorems.Thm_GlobalTheory_SqLB_gq_trans
-- name    : GlobalTheory.SqLB.gq_trans
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:22:06.512436+00:00
-- url     : https://prove2.me/theorems/1c55269b-caa2-43cc-abfb-fcf3ab6709b7
-- title:
--   Sq LB: gq trans
-- statement:
--   The Sq LB construction uses the gq trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSquareGeneratorThroughSquareIso.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSquareGeneratorThroughSquareIso.lean#L29-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSquareGeneratorThroughSquareIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SqLB
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem GlobalTheory.SqLB.gq_trans {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (f : Y ⟶ X') (y : Y) {j j' : L.ι} {k k' : L'.ι}
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
    gq w f y j k = gm (f ≫ F) y _ (L.g j j') ^ (2 : ℤ) * (gm f y _ (L'.g k k') ^ (2 : ℤ))⁻¹ * gq w f y j' k' := by sorry
