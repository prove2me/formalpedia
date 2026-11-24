-- Prove2me | Theorems.Thm_GlobalTheory_NatFun_HasCharts_mono
-- name    : GlobalTheory.NatFun.HasCharts.mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:30:14.408798+00:00
-- url     : https://prove2.me/theorems/b6ed6f4a-d41b-472d-aa53-1b897f84fd23
-- title:
--   Has Charts: mono
-- statement:
--   The Has Charts construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasChartsOfForallIsAffineOpen.lean#L163-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasChartsOfForallIsAffineOpen.lean#L163-L166

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

theorem GlobalTheory.NatFun.HasCharts.mono (h : HasCharts 𝒯 X)
    (hle : ∀ (A : Type) [CommRing A] [Algebra k A], 𝒯 A → 𝒯' A) : HasCharts 𝒯' X := by sorry
