-- Prove2me | Theorems.Thm_GlobalTheory_InvFieldRing_valR_add
-- name    : GlobalTheory.InvFieldRing.valR_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:10.454555+00:00
-- url     : https://prove2.me/theorems/e2bc47c2-aa4c-5c99-9f80-eb2386134db9
-- title:
--   Inv Field Ring: val R add
-- statement:
--   The Inv Field Ring construction uses the val R add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L23-L25

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

theorem GlobalTheory.InvFieldRing.valR_add (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f g : Γ(Y, V)) :
    valR x V (f + g) = valR x V f + valR x V g := by sorry
