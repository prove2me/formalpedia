-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_lin_fst_snd
-- name    : GlobalTheory.UnitLemma.InvAlg.lin_fst_snd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:34.03535+00:00
-- url     : https://prove2.me/theorems/6488072a-ffde-4363-b670-5353c434bf70
-- title:
--   Inv Alg: lin fst snd
-- statement:
--   The Inv Alg construction uses the lin fst snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LieLatticeProdComapInlAndMapSnd.lean#L23-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LieLatticeProdComapInlAndMapSnd.lean#L23-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ClearDenominators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LieLatticeProdComapInlAndMapSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory.UnitLemma.LinPair

theorem GlobalTheory.UnitLemma.InvAlg.lin_fst_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)),
    M ∈ (B₁.prod B₂).Lin →
    M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by sorry
