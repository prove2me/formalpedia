-- Prove2me | Theorems.Thm_GlobalTheory_AltCorank_finrank_inf_ker
-- name    : GlobalTheory.AltCorank.finrank_inf_ker
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:56:57.689821+00:00
-- url     : https://prove2.me/theorems/a9bf8dee-c4e9-4d27-842d-83519bdf4a59
-- title:
--   Alt Corank: finrank inf ker
-- statement:
--   The Alt Corank construction uses the finrank inf ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAlternatingFormLeftCorankLeOne.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAlternatingFormLeftCorankLeOne.lean#L43-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlternatingFormLeftCorankLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AltCorank
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.AltCorank.finrank_inf_ker [Module.Finite K V] (S : Submodule K V) (φ : V →ₗ[K] K) (u : V)
    (hu : u ∈ S) (hφ : φ u = 1) :
    finrank K (S ⊓ LinearMap.ker φ : Submodule K V) + 1 = finrank K S := by sorry
