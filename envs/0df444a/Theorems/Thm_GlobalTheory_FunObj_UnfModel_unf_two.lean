-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_UnfModel_unf_two
-- name    : GlobalTheory.FunObj.UnfModel.unf_two
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:50.22584+00:00
-- url     : https://prove2.me/theorems/65d39215-e211-548e-beae-79660331c9ad
-- title:
--   Unf Model: unf two
-- statement:
--   The Unf Model construction uses the unf two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MiddleNotMem.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MiddleNotMem.lean#L86-L97

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

theorem GlobalTheory.FunObj.UnfModel.unf_two (hm : G.m = 2) (hψ : ∀ a ∈ 𝒪[k], ψ a = 1) (hν : IsUnitVol ν) (S : G.Args → ℂ)
    (h1 : ∀ z, (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 1)
    (h0 : ∀ z, ¬ (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 0) (J : G.Level) (keep : Bool) :
    ∃ (hfin : (unfSupport ψ ν keep (Reps.through hs J fun _ => 1) S).Finite) (t : UnfTerm G),
      unf ψ ν keep _ S hfin = {t} ∧ t.coef = 1 ∧ t.datum 0 0 = 1 := by sorry
