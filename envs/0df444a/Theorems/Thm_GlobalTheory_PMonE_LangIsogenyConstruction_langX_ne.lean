-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_LangIsogenyConstruction_langX_ne
-- name    : GlobalTheory.PMonE.LangIsogenyConstruction.langX_ne
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:50.384815+00:00
-- url     : https://prove2.me/theorems/942debc8-9f7a-4177-91ba-dd6b9a42d5da
-- title:
--   Lang Isogeny Construction: lang X ne
-- statement:
--   The Lang Isogeny Construction construction uses the lang X ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LangXRoot.lean#L20-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LangXRoot.lean#L20-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangXRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LangIsogenyConstruction
open Polynomial
variable {k V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]

theorem GlobalTheory.PMonE.LangIsogenyConstruction.langX_ne (q : ℕ) (hq : 1 < q) (a : ℕ → k) (i : ℕ) (h : ∃ j ≤ i, a j ≠ 0) :
    langX q a i ≠ 0 := by sorry
