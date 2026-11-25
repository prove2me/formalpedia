-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_integral_eq_smul_finsum_coset
-- name    : GroundTheory.Automorphic.integral_eq_smul_finsum_coset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:13:06.556877+00:00
-- url     : https://prove2.me/theorems/41c31dcf-1d53-4604-822b-18e45a661b08
-- title:
--   Automorphic: integral eq smul finsum coset
-- statement:
--   The Automorphic construction uses the integral eq smul finsum coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarCosets.lean#L19-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarCosets.lean#L19-L44

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [IsFiniteMeasureOnCompacts μ]

theorem GroundTheory.Automorphic.integral_eq_smul_finsum_coset (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    ∫ g, f g ∂μ = μ.real (K : Set G) • ∑ᶠ x : G ⧸ (K : Subgroup G), f x.out := by sorry
