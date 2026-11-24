-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_inv_mem_dc
-- name    : GlobalTheory.SatakeWeyl.inv_mem_dc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:47:17.964199+00:00
-- url     : https://prove2.me/theorems/be1e5d73-319a-4eff-8281-827b60ea8a37
-- title:
--   Satake Weyl: inv mem dc
-- statement:
--   The Satake Weyl construction uses the inv mem dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L73-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L73-L87

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

theorem GlobalTheory.SatakeWeyl.inv_mem_dc [CompleteSpace L] {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (g : GU σ n) :
    ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g⁻¹ = k₁ * g * k₂ := by sorry
