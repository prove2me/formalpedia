-- Prove2me | Theorems.Thm_GlobalTheory_T_separable_charpoly_invAlgBaseChangeUnramified
-- name    : GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:34.005795+00:00
-- url     : https://prove2.me/theorems/09ac7681-1d1f-4668-bf5b-6fbeedee2317
-- title:
--   T: separable charpoly inv Alg Base Change Unramified
-- statement:
--   The T construction uses the separable charpoly inv Alg Base Change Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SeparableCharpolyInvAlgBaseChangeUnramifiedStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SeparableCharpolyInvAlgBaseChangeUnramifiedStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), B.P.Separable → (overExt φ B ψ hψ hσ).P.Separable := by sorry
