-- Prove2me | Theorems.Thm_GlobalTheory_T_isOpen_stabilizer_schwartzBruhat
-- name    : GlobalTheory.T.isOpen_stabilizer_schwartzBruhat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:36:23.363425+00:00
-- url     : https://prove2.me/theorems/90baa72f-e94f-480e-ad4e-5001636c4b52
-- title:
--   T: is Open stabilizer schwartz Bruhat
-- statement:
--   The T construction uses the is Open stabilizer schwartz Bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenStabilizerSchwartzBruhatStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenStabilizerSchwartzBruhatStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenStabilizerSchwartzBruhat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenStabilizerSchwartzBruhatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isOpen_stabilizer_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ} := by sorry
