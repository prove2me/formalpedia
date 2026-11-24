-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_integrable_opE_integrand
-- name    : GlobalTheory.RootEx.integrable_opE_integrand
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:21.709112+00:00
-- url     : https://prove2.me/theorems/41799649-ae6b-465d-b27f-85b487b07e99
-- title:
--   Root Ex: integrable op E integrand
-- statement:
--   The Root Ex construction uses the integrable op E integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingAffPtUncurry.lean#L111-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingAffPtUncurry.lean#L111-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c : ℕ}
open Classical

theorem GlobalTheory.RootEx.integrable_opE_integrand (p : ℕ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k)
    [ν.IsAddHaarMeasure] {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x₀ : Matrix n n' k) :
    Integrable (fun e => Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)) (Measure.pi fun _ => ν) := by sorry
