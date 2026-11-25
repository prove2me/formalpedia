-- Prove2me | Theorems.Thm_GlobalTheory_InvFieldRing_appLE_res
-- name    : GlobalTheory.InvFieldRing.appLE_res
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:05.460999+00:00
-- url     : https://prove2.me/theorems/cc00bfe5-db35-520b-bc39-13e70aa89e95
-- title:
--   Inv Field Ring: app LE res
-- statement:
--   The Inv Field Ring construction uses the app LE res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L92-L96

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
noncomputable section
open GlobalTheory GlobalTheory.InvFieldRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.InvFieldRing.appLE_res {Y Z : Scheme.{0}} (g : Z ⟶ Y) {V V' : Y.Opens} {W W' : Z.Opens} (h : V' ≤ V) (h' : W' ≤ W)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W' ≤ g ⁻¹ᵁ V') (f : Γ(Y, V)) :
    (g.appLE V' W' e').hom (resG Y h f) = resG Z h' ((g.appLE V W e).hom f) := by sorry
