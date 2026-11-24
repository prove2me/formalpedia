-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_integral_pi_pairs
-- name    : GlobalTheory.FunObj.integral_pi_pairs
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:35:43.698969+00:00
-- url     : https://prove2.me/theorems/8cee5af2-da45-49b6-a858-854108f41709
-- title:
--   Fun Obj: integral pi pairs
-- statement:
--   The Fun Obj construction uses the integral pi pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L130-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L130-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat

theorem GlobalTheory.FunObj.integral_pi_pairs (q : ℕ) : ∀ (E : ℕ → Type) [∀ j, MeasurableSpace (E j)] (μ : ∀ j, Measure (E j))
    [∀ j, SigmaFinite (μ j)] (H : ∀ j : Fin (2 * q), E j → E (j + 1) → ℂ) (L : E (2 * q) → ℂ),
    ∫ w : ∀ j : Fin (2 * q + 1), E j, (∏ j : Fin (2 * q), if Even j.1 then H j (w ⟨j, by omega⟩) (w ⟨j + 1, by omega⟩) else 1) *
      L (w ⟨2 * q, by omega⟩) ∂(Measure.pi fun j : Fin (2 * q + 1) => μ j) =
    (∏ j : Fin (2 * q), if Even j.1 then ∫ p : E j × E (j + 1), H j p.1 p.2 ∂((μ j).prod (μ (j + 1))) else 1) *
      ∫ u, L u ∂(μ (2 * q)) := by sorry
