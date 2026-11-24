-- Prove2me | Theorems.Thm_GlobalTheory_LinPair_secMap_apply
-- name    : GlobalTheory.LinPair.secMap_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:29:42.306311+00:00
-- url     : https://prove2.me/theorems/52737aeb-6157-42ba-a1e8-7c9dc5758be3
-- title:
--   Lin Pair: sec Map apply
-- statement:
--   The Lin Pair construction uses the sec Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/SecMapApply.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/SecMapApply.lean#L52-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SecMapApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.WeilM
open scoped Matrix
open GlobalTheory GlobalTheory.LinPair
variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] (c : E →ₐ[k] E)
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  [TopologicalSpace k]
variable {G H Y : Type} [Group G] [Group H]

theorem GlobalTheory.LinPair.secMap_apply (om : G × H →* Module.End ℂ (Y → ℂ)) (l : (Y → ℂ) →ₗ[ℂ] ℂ) (φ : Y → ℂ) (h : H) :
    secMap om l φ h = l (om (1, h) φ) := by sorry
