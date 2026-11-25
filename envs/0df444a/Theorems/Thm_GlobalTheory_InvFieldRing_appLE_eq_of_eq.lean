-- Prove2me | Theorems.Thm_GlobalTheory_InvFieldRing_appLE_eq_of_eq
-- name    : GlobalTheory.InvFieldRing.appLE_eq_of_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:31.54532+00:00
-- url     : https://prove2.me/theorems/dab7dccc-4fca-5bab-8dee-437d48210fd3
-- title:
--   Inv Field Ring: app LE eq of eq
-- statement:
--   The Inv Field Ring construction uses the app LE eq of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L81-L84

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

theorem GlobalTheory.InvFieldRing.appLE_eq_of_eq {Y Z : Scheme.{0}} {g g' : Z ⟶ Y} (hg : g = g') (V : Y.Opens) (W : Z.Opens)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W e = g'.appLE V W e' := by sorry
