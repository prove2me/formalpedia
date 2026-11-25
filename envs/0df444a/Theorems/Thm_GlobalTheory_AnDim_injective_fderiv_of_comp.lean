-- Prove2me | Theorems.Thm_GlobalTheory_AnDim_injective_fderiv_of_comp
-- name    : GlobalTheory.AnDim.injective_fderiv_of_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:35:50.492838+00:00
-- url     : https://prove2.me/theorems/3181aa14-7be5-509c-becd-ded0bc983d53
-- title:
--   An Dim: injective fderiv of comp
-- statement:
--   The An Dim construction uses the injective fderiv of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L79-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem GlobalTheory.AnDim.injective_fderiv_of_comp {a b c : ℕ} {F : (Fin a → ℂ) → Fin b → ℂ}
    {G : (Fin b → ℂ) → Fin c → ℂ} {H : (Fin a → ℂ) → Fin c → ℂ} {z : Fin a → ℂ}
    (hF : DifferentiableAt ℂ F z) (hG : DifferentiableAt ℂ G (F z)) (h : G ∘ F =ᶠ[𝓝 z] H)
    (hH : Function.Injective (fderiv ℂ H z)) : Function.Injective (fderiv ℂ F z) := by sorry
