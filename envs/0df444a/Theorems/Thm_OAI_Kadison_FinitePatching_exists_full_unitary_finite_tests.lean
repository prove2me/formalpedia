-- Prove2me | Theorems.Thm_OAI_Kadison_FinitePatching_exists_full_unitary_finite_tests
-- name    : OAI.Kadison.FinitePatching.exists_full_unitary_finite_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:54:24.462991+00:00
-- url     : https://prove2.me/theorems/5fa7842a-d919-4111-84fe-b94836c2c24e
-- title:
--   OAI.Kadison.FinitePatching.exists_full_unitary_finite_tests: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FinitePatching`, with `open scoped ComplexOrder Topology`, `open Filter`, `open Words`):
--
--   ```lean
--   theorem exists_full_unitary_finite_tests {J K : Type*} [Fintype J] [Fintype K]
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
--       (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
--         ∃ c : ℂ,b=algebraMap ℂ M c)
--       (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
--       (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
--       (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
--       (x : J → M) (k : K → ℤ) (hx : ∀ j,‖x j‖ ≤ 1)
--       (hcenter : ∀ j,τ (x j)=0) (hk : ∀ i,k i≠0)
--       (N : ℕ) {α : ℝ} (hα : 0<α) :
--       ∃ u : unitary M, ((u:M) : H →L[ℂ] H)∈R ∧
--         MomentBound τ x k (PartialUnitary.ofUnitary u) N α
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.FinitePatching.PartialUnitary.ofUnitary` and `OAI.Kadison.FinitePatching.Words.MomentBound` (definitions bundle `OAIQ039C035` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FinitePatching.exists_countable_unitary_tests` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C035

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

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

open Words

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n,Fintype (ι n)] [∀ n,LinearOrder (ι n)]
  [∀ n,Nonempty (ι n)]

variable (stage : ∀ n,Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range)

include hRM hτ hmono in
theorem exists_full_unitary_finite_tests {J K : Type*} [Fintype J] [Fintype K]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
    (x : J → M) (k : K → ℤ) (hx : ∀ j,‖x j‖ ≤ 1)
    (hcenter : ∀ j,τ (x j)=0) (hk : ∀ i,k i≠0)
    (N : ℕ) {α : ℝ} (hα : 0<α) :
    ∃ u : unitary M, ((u:M) : H →L[ℂ] H)∈R ∧
      MomentBound τ x k (PartialUnitary.ofUnitary u) N α := by
  sorry

end Kadison.FinitePatching

end

end
end

end OAI
end
