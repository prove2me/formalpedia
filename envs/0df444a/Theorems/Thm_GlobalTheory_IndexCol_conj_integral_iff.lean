-- Prove2me | Theorems.Thm_GlobalTheory_IndexCol_conj_integral_iff
-- name    : GlobalTheory.IndexCol.conj_integral_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:55.241793+00:00
-- url     : https://prove2.me/theorems/00dca051-a8ae-469d-8a44-ca4c879169c7
-- title:
--   Index Col: conj integral iff
-- statement:
--   The Index Col construction uses the conj integral iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLColumnCongruence.lean#L42-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLColumnCongruence.lean#L42-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndexCol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.IndexCol.conj_integral_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) (z : Matrix ι ι k) (hz : ∀ r s, z r s ∈ 𝒪[k]) :
    (∀ r s, ((diagGL (Pi.mulSingle t ϖ : ι → kˣ)).val * z * ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val) r s ∈ 𝒪[k]) ↔
      ∀ r, r ≠ t → valuation k (z r t) < 1 := by sorry
