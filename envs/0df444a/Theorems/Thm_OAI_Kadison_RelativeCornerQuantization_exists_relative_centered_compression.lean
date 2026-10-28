-- Prove2me | Theorems.Thm_OAI_Kadison_RelativeCornerQuantization_exists_relative_centered_compression
-- name    : OAI.Kadison.RelativeCornerQuantization.exists_relative_centered_compression
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:48:06.160183+00:00
-- url     : https://prove2.me/theorems/5bb8cb4a-8ba7-4df5-96b3-e9f6b3c9f834
-- title:
--   OAI.Kadison.RelativeCornerQuantization.exists_relative_centered_compression: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.RelativeCornerQuantization`, with `open scoped ComplexOrder InnerProductSpace Topology BigOperators`, `open Filter`, `open TracialL2`):
--
--   ```lean
--   theorem exists_relative_centered_compression
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
--       (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
--         ∃ c : ℂ, b=algebraMap ℂ M c)
--       (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
--       (N : VonNeumannAlgebra H)
--       (hstage : ∀ n a, (stage n a : H →L[ℂ] H)∈N)
--       (p : M) (hpN : (p : H →L[ℂ] H)∈N) (hp : IsStarProjection p)
--       (hpt : 0<(τ p).re)
--       (x : J → M) (hx : ∀ j, τ (x j)=0) (hpx : ∀ j,p*x j=x j) (hxp : ∀ j,x j*p=x j)
--       {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
--       ∃ f : M, (f : H →L[ℂ] H)∈N ∧ IsStarProjection f ∧ f ≤ p ∧
--         0<(τ f).re ∧ (τ f).re<η ∧ ∀ j, norm τ (f*x j*f)^2<ε^2*(τ f).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.TracialL2.norm` (definitions bundle `OAIQ039C017` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FinitePatching.exists_finite_word_patch` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C017
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.RelativeCornerQuantization

open TracialL2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

section Quantization

variable {J : Type*} [Fintype J]

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, LinearOrder (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

include hτ hmono in
theorem exists_relative_centered_compression
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (N : VonNeumannAlgebra H)
    (hstage : ∀ n a, (stage n a : H →L[ℂ] H)∈N)
    (p : M) (hpN : (p : H →L[ℂ] H)∈N) (hp : IsStarProjection p)
    (hpt : 0<(τ p).re)
    (x : J → M) (hx : ∀ j, τ (x j)=0) (hpx : ∀ j,p*x j=x j) (hxp : ∀ j,x j*p=x j)
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
    ∃ f : M, (f : H →L[ℂ] H)∈N ∧ IsStarProjection f ∧ f ≤ p ∧
      0<(τ f).re ∧ (τ f).re<η ∧ ∀ j, norm τ (f*x j*f)^2<ε^2*(τ f).re := by
  sorry

end Quantization

end Kadison.RelativeCornerQuantization

end

end
end

end OAI
end
