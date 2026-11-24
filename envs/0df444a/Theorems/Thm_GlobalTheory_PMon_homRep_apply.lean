-- Prove2me | Theorems.Thm_GlobalTheory_PMon_homRep_apply
-- name    : GlobalTheory.PMon.homRep_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:15.61208+00:00
-- url     : https://prove2.me/theorems/28350ee5-f1f6-47ab-8d07-2d9e39ebb88c
-- title:
--   PMon: hom Rep apply
-- statement:
--   The PMon construction uses the hom Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KroneckerTransposeMulVec.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KroneckerTransposeMulVec.lean#L55-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KroneckerTransposeMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.PMon
variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem GlobalTheory.PMon.homRep_apply {G : Type*} [Group G] (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) (g : G) :
    homRep ρ₁ ρ₂ g = homUnit (ρ₁ g) (ρ₂ g) := by sorry
