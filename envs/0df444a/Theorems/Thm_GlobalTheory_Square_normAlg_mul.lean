-- Prove2me | Theorems.Thm_GlobalTheory_Square_normAlg_mul
-- name    : GlobalTheory.Square.normAlg_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:25:03.510515+00:00
-- url     : https://prove2.me/theorems/ddf224f2-2ab6-5e6c-966a-00b40a71034a
-- title:
--   Square: norm Alg mul
-- statement:
--   The Square construction uses the norm Alg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L188-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L188-L192

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
attribute [instance] Co.finX
attribute [instance] Sq.finκ
omit [NumberField K]

theorem GlobalTheory.Square.normAlg_mul {κ X : Type} [Fintype κ] [Fintype X] (G : κ → κ → K) (gam : X → ℕ) (z : X → κ → K) (t : K) :
    normAlg G gam (fun x k => t * z x k) = t * star t * normAlg G gam z := by sorry
