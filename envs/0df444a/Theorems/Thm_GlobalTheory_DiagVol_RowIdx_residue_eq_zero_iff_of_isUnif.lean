-- Prove2me | Theorems.Thm_GlobalTheory_DiagVol_RowIdx_residue_eq_zero_iff_of_isUnif
-- name    : GlobalTheory.DiagVol.RowIdx.residue_eq_zero_iff_of_isUnif
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:02.475091+00:00
-- url     : https://prove2.me/theorems/80748632-ce90-41ae-a860-f3e4ff392614
-- title:
--   Row Idx: residue eq zero iff of is Unif
-- statement:
--   The Row Idx construction uses the residue eq zero iff of is Unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L48-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L48-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence
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
open GlobalTheory GlobalTheory.DiagVol GlobalTheory.DiagVol.RowIdx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.DiagVol.RowIdx.residue_eq_zero_iff_of_isUnif {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : k) (ha : a ∈ 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] ⟨a, ha⟩ = 0 ↔ (ϖ : k)⁻¹ * a ∈ 𝒪[k] := by sorry
