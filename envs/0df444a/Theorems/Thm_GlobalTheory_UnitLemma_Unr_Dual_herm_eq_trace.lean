-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_Dual_herm_eq_trace
-- name    : GlobalTheory.UnitLemma.Unr.Dual.herm_eq_trace
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:35:33.11681+00:00
-- url     : https://prove2.me/theorems/84e8cb30-1e47-4cce-a851-a251c54ccc55
-- title:
--   Dual: herm eq trace
-- statement:
--   The Dual construction uses the herm eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianDualInvAlgBaseChangeUnramifiedIff.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianDualInvAlgBaseChangeUnramifiedIff.lean#L33-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnramifiedQuadraticLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianDualInvAlgBaseChangeUnramifiedIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.Dual
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr

theorem GlobalTheory.UnitLemma.Unr.Dual.herm_eq_trace {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (B : InvAlg K)
    (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e))
    (x y z : B.A) :
    B.herm x y z = @Algebra.trace K.E K'.E _ _ φ.toAlgebra ((overExt φ B ψ hψ hσ).herm x y z) := by sorry
