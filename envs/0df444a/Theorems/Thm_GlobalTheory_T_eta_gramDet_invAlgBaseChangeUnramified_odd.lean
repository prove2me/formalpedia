-- Prove2me | Theorems.Thm_GlobalTheory_T_eta_gramDet_invAlgBaseChangeUnramified_odd
-- name    : GlobalTheory.T.eta_gramDet_invAlgBaseChangeUnramified_odd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:48:18.234668+00:00
-- url     : https://prove2.me/theorems/aa094d24-03db-462c-8fa9-ab97175c60d9
-- title:
--   T: eta gram Det inv Alg Base Change Unramified odd
-- statement:
--   The T construction uses the eta gram Det inv Alg Base Change Unramified odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaGramDetInvAlgBaseChangeUnramifiedOddStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaGramDetInvAlgBaseChangeUnramifiedOddStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOddStatement
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

theorem GlobalTheory.T.eta_gramDet_invAlgBaseChangeUnramified_odd : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (x : B.Aˣ), B.σ (x : B.A) = x → K'.eta ((overExt φ B ψ hψ hσ).gramDet (x : B.A)) = K.eta (B.gramDet (x : B.A)) := by sorry
