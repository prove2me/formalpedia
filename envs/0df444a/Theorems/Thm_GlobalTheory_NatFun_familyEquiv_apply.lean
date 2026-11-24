-- Prove2me | Theorems.Thm_GlobalTheory_NatFun_familyEquiv_apply
-- name    : GlobalTheory.NatFun.familyEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:02.617676+00:00
-- url     : https://prove2.me/theorems/9daeb387-0aad-44cf-a049-359e4e83bf79
-- title:
--   Nat Fun: family Equiv apply
-- statement:
--   The Nat Fun construction uses the family Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasChartsOfForallIsAffineOpen.lean#L359-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasChartsOfForallIsAffineOpen.lean#L359-L361

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp)
open GlobalTheory GlobalTheory.NatFun
variable {k : Type} [CommRing k]
variable {𝒯 𝒯' : AlgClass k} {X : Over (Spec (CommRingCat.of k))}

theorem GlobalTheory.NatFun.familyEquiv_apply (h𝒯 : 𝒯.StableAway) (hX : HasCharts 𝒯 X) (s : Γ(X.left, ⊤))
    (A : Type) [CommRing A] [Algebra k A] (hA : 𝒯 A) (x : sp A ⟶ X) :
    (familyEquiv h𝒯 hX s).app A hA x = value x s := by sorry

attribute [defeq] GlobalTheory.NatFun.familyEquiv_apply
