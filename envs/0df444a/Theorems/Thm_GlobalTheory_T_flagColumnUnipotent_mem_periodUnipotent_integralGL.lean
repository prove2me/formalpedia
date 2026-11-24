-- Prove2me | Theorems.Thm_GlobalTheory_T_flagColumnUnipotent_mem_periodUnipotent_integralGL
-- name    : GlobalTheory.T.flagColumnUnipotent_mem_periodUnipotent_integralGL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:40:46.689738+00:00
-- url     : https://prove2.me/theorems/6fb95ea8-8329-4bd8-b441-c2e3203bf763
-- title:
--   T: flag Column Unipotent mem period Unipotent integral GL
-- statement:
--   The T construction uses the flag Column Unipotent mem period Unipotent integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagColumnUnipotentMemPeriodUnipotentIntegralGLStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagColumnUnipotentMemPeriodUnipotentIntegralGLStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagColumnUnipotentMemPeriodUnipotentIntegralGL
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagColumnUnipotentMemPeriodUnipotentIntegralGLStatement
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

theorem GlobalTheory.T.flagColumnUnipotent_mem_periodUnipotent_integralGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k), (∀ r, y r ∈ 𝒪[k]) → (∀ r, ¬ ordL c r < ordL c t → y r = 0) → ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0) := by sorry
