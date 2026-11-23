-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_FontW_Dv_map
-- name    : GlobalTheory.Cyc.FontW.Dv_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:55.207703+00:00
-- url     : https://prove2.me/theorems/b4a73cc6-89b3-43de-9c3e-4ba52543b78a
-- title:
--   Font W: Dv map
-- statement:
--   The Font W construction uses the Dv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRight.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRight.lean#L11-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW

theorem GlobalTheory.Cyc.FontW.Dv_map {l r : ℕ} {M M' F : Type*} [AddCommGroup M] [AddCommGroup M'] [FunLike F M M']
    [AddMonoidHomClass F M M'] (f : F) {x : M} (hx : x ∈ Dv l r M) : f x ∈ Dv l r M' := by sorry
