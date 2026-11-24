-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_OpELevi_integral_right
-- name    : GlobalTheory.RootEx.OpELevi.integral_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:25:31.215804+00:00
-- url     : https://prove2.me/theorems/05a8e5a0-cb6c-4ab8-8a26-9e83bc9fc4b6
-- title:
--   Op ELevi: integral right
-- statement:
--   The Op ELevi construction uses the integral right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L229-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L229-L256

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
omit [DecidableEq n]

theorem GlobalTheory.RootEx.OpELevi.integral_right (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (A : Matrix n' n' k) (u : kˣ) (hu : A.det = u)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun x => Φ (x * (fromBlocks A 0 0 1 :
        Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k))) x₀ =
      ((nabs k u ^ Fintype.card {l : Fin c // l.val + 1 < p})⁻¹ : ℝ) • opE ψ ν p Φ (x₀ * A) := by sorry
