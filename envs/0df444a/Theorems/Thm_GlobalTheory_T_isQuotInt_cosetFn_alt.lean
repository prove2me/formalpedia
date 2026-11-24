-- Prove2me | Theorems.Thm_GlobalTheory_T_isQuotInt_cosetFn_alt
-- name    : GlobalTheory.T.isQuotInt_cosetFn_alt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:23.87358+00:00
-- url     : https://prove2.me/theorems/4a9d606e-9adb-4ab4-8e07-975714647fde
-- title:
--   T: is Quot Int coset Fn alt
-- statement:
--   The T construction uses the is Quot Int coset Fn alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsQuotIntCosetFnStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsQuotIntCosetFnStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsQuotIntCosetFn
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsQuotIntCosetFnStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isQuotInt_cosetFn_alt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ (h : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) (v : ℝ), v ≠ 0 → (∀ u₀ ∈ N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : N k n c 1, (Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * embX c g₀)) ∂(volN ν n c 1)) ∂m = ((deltaR c g₀ * v : ℝ) : ℂ)) → ∀ (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ), IsCosetFn J h f → IsQuotInt ν m μG 1 f ((((μG J).toReal / v : ℝ) : ℂ) * f h) := by sorry
