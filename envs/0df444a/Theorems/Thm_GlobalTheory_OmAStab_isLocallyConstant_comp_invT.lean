-- Prove2me | Theorems.Thm_GlobalTheory_OmAStab_isLocallyConstant_comp_invT
-- name    : GlobalTheory.OmAStab.isLocallyConstant_comp_invT
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:36:36.403606+00:00
-- url     : https://prove2.me/theorems/ba4f4f70-6f1c-475b-9be3-ff654880ff9a
-- title:
--   Om AStab: is Locally Constant comp inv T
-- statement:
--   The Om AStab construction uses the is Locally Constant comp inv T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenStabilizerSchwartzBruhat.lean#L30-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenStabilizerSchwartzBruhat.lean#L30-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenStabilizerSchwartzBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM
open GlobalTheory GlobalTheory.OmAStab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.OmAStab.isLocallyConstant_comp_invT {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    {Φ : Matrix A D k → ℂ} (hΦ : Φ ∈ SB (Matrix A D k)) :
    IsLocallyConstant fun h : GL D k => fun X : Matrix A D k => Φ (X * (invT h).val) := by sorry
