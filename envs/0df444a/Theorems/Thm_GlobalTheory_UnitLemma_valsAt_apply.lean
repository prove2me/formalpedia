-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_valsAt_apply
-- name    : GlobalTheory.UnitLemma.valsAt_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:35.46636+00:00
-- url     : https://prove2.me/theorems/380e75b3-1821-4158-93d0-511936bea92b
-- title:
--   Unit Lemma: vals At apply
-- statement:
--   The Unit Lemma construction uses the vals At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValsAtApply.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValsAtApply.lean#L19-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValsAtApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.valsAt_apply {G : Type} [Group G] {ι : Type} (w : ι → G →* Multiplicative ℤ) {r : ℕ}
    (e : Fin r → ι) (x : G) (j : Fin r) :
    Multiplicative.toAdd (valsAt w e x) j = Multiplicative.toAdd (w (e j) x) := by sorry
