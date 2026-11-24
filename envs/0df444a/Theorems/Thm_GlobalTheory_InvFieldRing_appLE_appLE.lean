-- Prove2me | Theorems.Thm_GlobalTheory_InvFieldRing_appLE_appLE
-- name    : GlobalTheory.InvFieldRing.appLE_appLE
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:20:46.344025+00:00
-- url     : https://prove2.me/theorems/8371aa7b-80f9-4afd-99cf-dff9c67c1466
-- title:
--   Inv Field Ring: app LE app LE
-- statement:
--   The Inv Field Ring construction uses the app LE app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L86-L90

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

theorem GlobalTheory.InvFieldRing.appLE_appLE {Y Z Q : Scheme.{0}} (g : Z ⟶ Y) (k : Q ⟶ Z) (V : Y.Opens) (W : Z.Opens) (W' : Q.Opens)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W' ≤ k ⁻¹ᵁ W) (f : Γ(Y, V)) :
    (k.appLE W W' e').hom ((g.appLE V W e).hom f) = ((k ≫ g).appLE V W' (e'.trans (k.preimage_mono e))).hom f := by sorry
