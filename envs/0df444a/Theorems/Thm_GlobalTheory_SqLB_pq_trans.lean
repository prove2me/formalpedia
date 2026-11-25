-- Prove2me | Theorems.Thm_GlobalTheory_SqLB_pq_trans
-- name    : GlobalTheory.SqLB.pq_trans
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:21:22.574262+00:00
-- url     : https://prove2.me/theorems/f2e57ea0-659a-40bb-bde5-019c9aae7780
-- title:
--   Sq LB: pq trans
-- statement:
--   The Sq LB construction uses the pq trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSquareGeneratorThroughSquareIso.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSquareGeneratorThroughSquareIso.lean#L44-L56

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

theorem GlobalTheory.SqLB.pq_trans {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y)
    (z : Z) {p p' : K → L.ι} {q q' : K → L'.ι} (hp : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p') (hq : r z ∈ LB.wchart L' φ' q) (hq' : r z ∈ LB.wchart L' φ' q') :
    pq w φ' ε r z p q = trF (fun k => φ' k ≫ F) (fun k => 2 * ε k) r z p p' *
      (trF φ' (fun k => 2 * ε k) r z q q')⁻¹ * pq w φ' ε r z p' q' := by sorry
