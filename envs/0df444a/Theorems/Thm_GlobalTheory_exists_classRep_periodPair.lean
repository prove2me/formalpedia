-- Prove2me | Theorems.Thm_GlobalTheory_exists_classRep_periodPair
-- name    : GlobalTheory.exists_classRep_periodPair
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:29.74091+00:00
-- url     : https://prove2.me/theorems/bc0a89eb-f716-4173-96ea-430c2aadee6e
-- title:
--   Global Theory: exists class Rep period Pair
-- statement:
--   The Global Theory construction uses the exists class Rep period Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean#L70-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}

theorem GlobalTheory.exists_classRep_periodPair (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
    (c : ClassGroup (𝓞 K)) : ∃ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair),
      ClassGroup.mk K 𝔞 = c ∧ (L.lattice : Set ℂ) = σ '' 𝔞.1 := by sorry
