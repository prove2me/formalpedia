-- Prove2me | Theorems.Thm_GlobalTheory_T_flagRowUnipotent_mem_periodUnipotent_integralGL
-- name    : GlobalTheory.T.flagRowUnipotent_mem_periodUnipotent_integralGL
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:40:54.347135+00:00
-- url     : https://prove2.me/theorems/a581b30c-d292-40e6-92ca-8eb63d5d9416
-- title:
--   T: flag Row Unipotent mem period Unipotent integral GL
-- statement:
--   The T construction uses the flag Row Unipotent mem period Unipotent integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagRowUnipotentMemPeriodUnipotentIntegralGLStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagRowUnipotentMemPeriodUnipotentIntegralGLStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagRowUnipotentMemPeriodUnipotentIntegralGL
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagRowUnipotentMemPeriodUnipotentIntegralGLStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.flagRowUnipotent_mem_periodUnipotent_integralGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k), (∀ s, y s ∈ 𝒪[k]) → (∀ s, ¬ ordL c t < ordL c s → y s = 0) → ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0) := by sorry
