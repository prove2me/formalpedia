-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Unram_opE_unramified
-- name    : GlobalTheory.RootEx.Unram.opE_unramified
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:53.806492+00:00
-- url     : https://prove2.me/theorems/451fa761-715b-4313-bad5-de89dea4d4ae
-- title:
--   Unram: op E unramified
-- statement:
--   The Unram construction uses the op E unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L352-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L352-L385

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.RootEx.Unram.opE_unramified : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (_ : Φ = Set.indicator {x | ∀ r s, valuation k (x r s) ≤ 1} 1), (∀ (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k), opE ψ ν p (om μ 1 h Φ) x₀ ≠ 0 → ∃ r ∈ R k n c p, ∃ w ∈ KO k (n ⊕ Fin c), h = r * w) ∧ opE ψ ν p Φ = Set.indicator {x | ∀ r s, valuation k (x r s) ≤ 1} 1 ∧ ∀ β : n → k, p + 1 ≤ c → opE ψ ν (p + 1) (om μ 1 (colE c (p + 1) β) Φ) = Set.indicator {x | (∀ r s, valuation k (x r s) ≤ 1) ∧ ∀ r, valuation k (β r) ≤ 1} 1 := by sorry
