-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_all_character_decorrelation
-- name    : OAI.Ostmann.PublishedProgressionInput.all_character_decorrelation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:21:41.089874+00:00
-- url     : https://prove2.me/theorems/5d376e7d-193b-468c-a529-2d2d9569fcda
-- title:
--   OAI.Ostmann.PublishedProgressionInput.all_character_decorrelation: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.all_character_decorrelation` of [lean/OAI/NumberTheory/Ostmann/Characters/AllCharacterDecorrelation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/AllCharacterDecorrelation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators Topology`):
--
--   ```lean
--   theorem PublishedProgressionInput.all_character_decorrelation
--       (P0 : PublishedProgressionInput)
--       (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
--       {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
--       (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
--       (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
--       (hquad : (fun T => closedQuadraticBandMass Aset N₀ T) =o[atTop] (fun T : ℝ => T))
--       (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
--       (fun L => tailCharacterBandMass Aset N₀ α β L) =o[atTop] (fun L : ℝ => L)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.PublishedSummandSizeBound` and `OAI.Ostmann.tailResidues` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.negTailResidues` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.closedQuadraticBandMass` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.tailCharacterBandMass` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.EventuallyPrimeSumset` (the published bundle `Def_OstmannComplete`).
--
--   **Used by.** The proofs of `OAI.Ostmann.EventuallyPrimeSumset.initial_broad_prior_centers` and `OAI_Ostmann_EventuallyPrimeSumset_tail_spectator_pool` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/AllCharacterDecorrelation.lean (declaration OAI.Ostmann.PublishedProgressionInput.all_character_decorrelation)

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D007

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

theorem PublishedProgressionInput.all_character_decorrelation
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (hquad : (fun T => closedQuadraticBandMass Aset N₀ T) =o[atTop] (fun T : ℝ => T))
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    (fun L => tailCharacterBandMass Aset N₀ α β L) =o[atTop] (fun L : ℝ => L) := by
  sorry

end Ostmann

end OAI
end
