-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_UnfModel_vacuum_term
-- name    : GlobalTheory.FunObj.UnfModel.vacuum_term
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:22.752972+00:00
-- url     : https://prove2.me/theorems/88c76e9c-5bc6-4883-b97e-bebdaff22c86
-- title:
--   Unf Model: vacuum term
-- statement:
--   The Unf Model construction uses the vacuum term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MiddleNotMem.lean#L74-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MiddleNotMem.lean#L74-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {G : Grid k} (hs : 1 ≤ G.s) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

theorem GlobalTheory.FunObj.UnfModel.vacuum_term (hψ : ∀ a ∈ 𝒪[k], ψ a = 1) (hν : IsUnitVol ν) (S : G.Args → ℂ)
    (h1 : ∀ z, (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 1)
    (h0 : ∀ z, ¬ (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 0) (J : G.Level) (keep : Bool) :
    (unfTerm ψ ν keep (Reps.through hs J fun _ => 1) S fun _ => DoubleCoset.mk _ _ 1).datum 0 0 = 1 ∧
    (fun _ => DoubleCoset.mk _ _ 1) ∈ unfSupport ψ ν keep (Reps.through hs J fun _ => 1) S := by sorry
