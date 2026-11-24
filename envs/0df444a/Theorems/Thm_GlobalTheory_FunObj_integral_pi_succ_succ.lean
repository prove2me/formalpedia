-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_integral_pi_succ_succ
-- name    : GlobalTheory.FunObj.integral_pi_succ_succ
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:16.881185+00:00
-- url     : https://prove2.me/theorems/d6385972-84a6-4848-8f8d-4b980c72a517
-- title:
--   Fun Obj: integral pi succ succ
-- statement:
--   The Fun Obj construction uses the integral pi succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L110-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L110-L123

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

theorem GlobalTheory.FunObj.integral_pi_succ_succ {n : ℕ} {E : Fin (n + 2) → Type} [∀ j, MeasurableSpace (E j)] (μ : ∀ j, Measure (E j))
    [∀ j, SigmaFinite (μ j)] (F : (∀ j, E j) → ℂ) :
    ∫ w, F w ∂(Measure.pi μ) =
      ∫ p : (E 0 × E (Fin.succ 0)) × (∀ j : Fin n, E j.succ.succ), F (Fin.cons p.1.1 (Fin.cons p.1.2 p.2))
        ∂(((μ 0).prod (μ (Fin.succ 0))).prod (Measure.pi fun j => μ j.succ.succ)) := by sorry
