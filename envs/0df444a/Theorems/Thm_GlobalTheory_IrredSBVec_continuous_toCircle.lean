-- Prove2me | Theorems.Thm_GlobalTheory_IrredSBVec_continuous_toCircle
-- name    : GlobalTheory.IrredSBVec.continuous_toCircle
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:22:00.195532+00:00
-- url     : https://prove2.me/theorems/2dcc3671-7c30-4931-9f50-1e860a574bf3
-- title:
--   Irred SBVec: continuous to Circle
-- statement:
--   The Irred SBVec construction uses the continuous to Circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatVectorIrreducibleTranslationsChara.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatVectorIrreducibleTranslationsChara.lean#L32-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatVectorIrreducibleTranslationsChara
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IrredSBVec
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.IrredSBVec.continuous_toCircle (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (hψ : Continuous ψ0) :
    Continuous (toCircle ψ0 h1) := by sorry
