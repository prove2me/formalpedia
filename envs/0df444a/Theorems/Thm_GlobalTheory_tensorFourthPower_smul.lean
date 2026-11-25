-- Prove2me | Theorems.Thm_GlobalTheory_tensorFourthPower_smul
-- name    : GlobalTheory.tensorFourthPower_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:16.343012+00:00
-- url     : https://prove2.me/theorems/43488617-0135-43b9-b618-a45f8397ba3f
-- title:
--   Global Theory: tensor Fourth Power smul
-- statement:
--   The Global Theory construction uses the tensor Fourth Power smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/LocalNormalizationIntegralScalar.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/LocalNormalizationIntegralScalar.lean#L8-L12

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AlgebraicTheory_StatementNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LocalNormalizationIntegralScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Formalism.L2.AlgTh

theorem GlobalTheory.tensorFourthPower_smul {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) (θ : (n → ℂ) → ℂ) :
    Formalism.L2.Th1.H.tens4 (c • θ) = c ^ 4 • Formalism.L2.Th1.H.tens4 θ := by sorry
