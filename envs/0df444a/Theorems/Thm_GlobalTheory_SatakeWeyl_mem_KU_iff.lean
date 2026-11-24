-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_mem_KU_iff
-- name    : GlobalTheory.SatakeWeyl.mem_KU_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:12:26.056147+00:00
-- url     : https://prove2.me/theorems/e1b5c0ed-901f-4d8e-9116-a86308b9cbad
-- title:
--   Satake Weyl: mem KU iff
-- statement:
--   The Satake Weyl construction uses the mem KU iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L60-L71

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem GlobalTheory.SatakeWeyl.mem_KU_iff (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) :
    g ∈ KU σ n ↔ ∀ i j, mat g i j ∈ intL L := by sorry
