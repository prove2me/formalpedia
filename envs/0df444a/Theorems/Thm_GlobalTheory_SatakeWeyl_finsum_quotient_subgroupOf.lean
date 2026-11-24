-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_finsum_quotient_subgroupOf
-- name    : GlobalTheory.SatakeWeyl.finsum_quotient_subgroupOf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:48:38.747987+00:00
-- url     : https://prove2.me/theorems/50ec3c1e-52e2-4bb0-b004-b38cf6006a4c
-- title:
--   Satake Weyl: finsum quotient subgroup Of
-- statement:
--   The Satake Weyl construction uses the finsum quotient subgroup Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexCosetSumUnimodularityOfFiniteIndex.lean#L9-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexCosetSumUnimodularityOfFiniteIndex.lean#L9-L37

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexCosetSumUnimodularityOfFiniteIndex
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl

theorem GlobalTheory.SatakeWeyl.finsum_quotient_subgroupOf {A : Type} [Group A] (Γ W : Subgroup A) (F : A → ℂ)
    (hΓ : ∀ a, F a ≠ 0 → a ∈ Γ) (hF : ∀ w ∈ W, ∀ a, F (a * w) = F a) :
    ∑ᶠ y : A ⧸ W, F y.out = ∑ᶠ y : Γ ⧸ W.subgroupOf Γ, F (y.out : Γ) := by sorry
