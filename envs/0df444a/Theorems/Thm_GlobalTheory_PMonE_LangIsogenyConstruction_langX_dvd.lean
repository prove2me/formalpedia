-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_LangIsogenyConstruction_langX_dvd
-- name    : GlobalTheory.PMonE.LangIsogenyConstruction.langX_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:32.615936+00:00
-- url     : https://prove2.me/theorems/50177570-17a9-48f8-9f45-f94e02db096f
-- title:
--   Lang Isogeny Construction: lang X dvd
-- statement:
--   The Lang Isogeny Construction construction uses the lang X dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LangXRoot.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LangXRoot.lean#L14-L18

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

theorem GlobalTheory.PMonE.LangIsogenyConstruction.langX_dvd (q : ℕ) (hq : 1 < q) (a : ℕ → k) (i : ℕ) : (X : k[X]) ^ q ∣ langX q a i := by sorry
