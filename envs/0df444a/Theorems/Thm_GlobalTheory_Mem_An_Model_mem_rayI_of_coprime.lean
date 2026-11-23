-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_Model_mem_rayI_of_coprime
-- name    : GlobalTheory.Mem.An.Model.mem_rayI_of_coprime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:40.21821+00:00
-- url     : https://prove2.me/theorems/527fc524-df9f-44d0-9e98-f573854a04df
-- title:
--   Model: mem ray I of coprime
-- statement:
--   The Model construction uses the mem ray I of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L40-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L40-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model

theorem GlobalTheory.Mem.An.Model.mem_rayI_of_coprime {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) (J : Ideal (𝓞 K)) :
    J ≠ 0 → J ⊔ 𝔮 = ⊤ → ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      (I : FractionalIdeal (𝓞 K)⁰ K) = (J : FractionalIdeal (𝓞 K)⁰ K) → I ∈ rayI 𝔮 := by sorry
