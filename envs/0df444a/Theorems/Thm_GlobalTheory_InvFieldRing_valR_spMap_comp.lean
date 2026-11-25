-- Prove2me | Theorems.Thm_GlobalTheory_InvFieldRing_valR_spMap_comp
-- name    : GlobalTheory.InvFieldRing.valR_spMap_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:15.681157+00:00
-- url     : https://prove2.me/theorems/91839eaa-993f-5b6e-8433-5e4681ed714f
-- title:
--   Inv Field Ring: val R sp Map comp
-- statement:
--   The Inv Field Ring construction uses the val R sp Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L49-L58

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
variable {A : Type} [CommRing A] {Y : Scheme.{0}}

theorem GlobalTheory.InvFieldRing.valR_spMap_comp {A' : Type} [CommRing A'] (ψ : A →+* A') (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (f : Γ(Y, V)) : valR (spMap ψ ≫ x) V f = ψ (valR x V f) := by sorry
