-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_levi_mul
-- name    : GlobalTheory.InertZeta.levi_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:20:49.894474+00:00
-- url     : https://prove2.me/theorems/e29d5a98-a5ce-4141-a958-525cbb32e3d2
-- title:
--   Inert Zeta: levi mul
-- statement:
--   The Inert Zeta construction uses the levi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SphericalInductionTransitivityOfLeviExists.lean#L34-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SphericalInductionTransitivityOfLeviExists.lean#L34-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SphericalInductionTransitivityOfLeviExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem GlobalTheory.InertZeta.levi_mul {ϖ : L} (hϖ : ϖ ≠ 0) {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g m)
    (h' : IsLeviElt ϖ a' g' m') : IsLeviElt ϖ (a + a') (g * g') (m * m') := by sorry
