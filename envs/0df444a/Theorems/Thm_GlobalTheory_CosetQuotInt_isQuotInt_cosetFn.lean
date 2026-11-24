-- Prove2me | Theorems.Thm_GlobalTheory_CosetQuotInt_isQuotInt_cosetFn
-- name    : GlobalTheory.CosetQuotInt.isQuotInt_cosetFn
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:09:38.709865+00:00
-- url     : https://prove2.me/theorems/7beddd28-f81b-407a-b239-bc1c30938899
-- title:
--   Coset Quot Int: is Quot Int coset Fn
-- statement:
--   The Coset Quot Int construction uses the is Quot Int coset Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsQuotIntCosetFn.lean#L13-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsQuotIntCosetFn.lean#L13-L137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsQuotIntCosetFn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.CosetQuotInt
open MeasureTheory ValuativeRel Matrix Topology

theorem GlobalTheory.CosetQuotInt.isQuotInt_cosetFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J)
    (h : GL (n ⊕ Fin c) k)
    (m : Measure (GL n k)) (v : ℝ) (hv : v ≠ 0)
    (hvol : ∀ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1, ∀ g₀ : GL n k, ∫ g,
      (∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
      (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
        (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
          (u₀ * _root_.GlobalTheory.RootEx.embX c g₀))
          ∂(_root_.GlobalTheory.RootEx.volN ν n c 1)) ∂m
          = ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ * v : ℝ) : ℂ))
    (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ)
    (hf : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCosetFn J h f) :
    _root_.GlobalTheory.RootEx.IsQuotInt ν m μG 1 f ((((μG J).toReal / v : ℝ) : ℂ) * f h) := by sorry
