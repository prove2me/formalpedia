-- Prove2me | Theorems.Thm_GlobalTheory_FlatFibreRegular_mem_of_mul_mem
-- name    : GlobalTheory.FlatFibreRegular.mem_of_mul_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:50:21.56781+00:00
-- url     : https://prove2.me/theorems/97a9c080-0360-527d-a059-c8989ab2e479
-- title:
--   Flat Fibre Regular: mem of mul mem
-- statement:
--   The Flat Fibre Regular construction uses the mem of mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L138-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L138-L189

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatFibreRegular

theorem GlobalTheory.FlatFibreRegular.mem_of_mul_mem {B : Type} [CommRing B] (u : Ideal B) [u.IsPrime] (I₀ : Ideal B)
    (hrad : I₀.IsRadical) (g : B) (hg : ∀ Q ∈ I₀.minimalPrimes, Q ≤ u → g ∉ Q)
    (y : Localization.AtPrime u)
    (hy : algebraMap B _ g * y ∈ I₀.map (algebraMap B (Localization.AtPrime u))) :
    y ∈ I₀.map (algebraMap B (Localization.AtPrime u)) := by sorry
