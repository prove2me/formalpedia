-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_traceZero_eq_map
-- name    : GlobalTheory.CompanionTheory.InertZeta.traceZero_eq_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:02:43.795798+00:00
-- url     : https://prove2.me/theorems/22a682e9-7a31-43af-9cdf-52415802e120
-- title:
--   Inert Zeta: trace Zero eq map
-- statement:
--   The Inert Zeta construction uses the trace Zero eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/TraceIndexFormula.lean#L11-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/TraceIndexFormula.lean#L11-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceZeroIntegersModUniformizerCardOfCardSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_TraceIndexFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.CompanionTheory.InertZeta.traceZero_eq_map {σ : L →+* L} {c : L} (hc : c ≠ 0) (hσ : σ c = c) :
    traceZero σ c =
      ((intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker).map (AddMonoidHom.mulLeft c⁻¹) := by sorry
