-- Prove2me | Theorems.Thm_GlobalTheory_WeilCont_pureA_adeleJoin
-- name    : GlobalTheory.WeilCont.pureA_adeleJoin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:21.446478+00:00
-- url     : https://prove2.me/theorems/127893f8-60d6-458a-afa8-3e3209329a3c
-- title:
--   Weil Cont: pure A adele Join
-- statement:
--   The Weil Cont construction uses the pure A adele Join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsContOnOfLocal.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsContOnOfLocal.lean#L16-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsContOnOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped Classical
open GlobalTheory GlobalTheory.WeilCont
variable (F : Type) [Field F] [NumberField F] {κ : Type}

theorem GlobalTheory.WeilCont.pureA_adeleJoin (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.pureA F f g (adeleJoin F x y) = f x * g y := by sorry
