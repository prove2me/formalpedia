-- Prove2me | Theorems.Thm_OAI_Kadison_FinitePatching_exists_finite_word_patch
-- name    : OAI.Kadison.FinitePatching.exists_finite_word_patch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:54:39.356987+00:00
-- url     : https://prove2.me/theorems/55a3e115-bcba-4727-b83c-d4959844ecbf
-- title:
--   OAI.Kadison.FinitePatching.exists_finite_word_patch: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FinitePatching`, with `open scoped ComplexOrder Topology`, `open Filter`, `open Words`):
--
--   ```lean
--   theorem exists_finite_word_patch {J K : Type*} [Fintype J] [Fintype K]
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
--       (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
--         ∃ c : ℂ,b=algebraMap ℂ M c)
--       (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
--       (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
--       (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
--       (x : J → M) (k : K → ℤ) (hk : ∀ i,k i≠0)
--       (v : PartialUnitary M) (hvR : (v.support : H →L[ℂ] H)∈R)
--       (hrest : 0<(τ (1-v.support)).re) (N : ℕ) {δ ζ : ℝ} (hδ : 0<δ) (hζ : 0<ζ) :
--       ∃ w : PartialUnitary M, (w.val : H →L[ℂ] H)∈R ∧
--         (w.support : H →L[ℂ] H)∈R ∧ w.support ≤ 1-v.support ∧
--         v.support*w.support=0 ∧ 0<(τ w.support).re ∧ (τ w.support).re<ζ ∧
--         (∀ i,‖τ (w.power (k i))‖ ≤ δ*(τ w.support).re) ∧
--         (∀ (s : List (Letter J K)) (j : J),s.length ≤ N →
--           TracialL2.norm τ (w.support*cornerCenter τ (1-v.support)
--             (word x k v s*x j)*w.support)^2 ≤ δ^2*(τ w.support).re) ∧
--         (∀ (s t : List (Letter J K)) (j : J) (i : K),s.length ≤ N → t.length ≤ N →
--           ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ δ*(τ w.support).re)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.FinitePatching.PartialUnitary` and `OAI.Kadison.FinitePatching.PartialUnitary.power` (definitions bundle `OAIQ039C009` of this split); `OAI.Kadison.FinitePatching.cornerCenter` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialL2.norm` (definitions bundle `OAIQ039C017` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.FinitePatching.Words.Letter` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FinitePatching.Words.word` (definitions bundle `OAIQ039C035` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FinitePatching.exists_almost_full_finite_tests` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C017
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
theorem exists_finite_word_patch {J K : Type*} [Fintype J] [Fintype K]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
    (x : J → M) (k : K → ℤ) (hk : ∀ i,k i≠0)
    (v : PartialUnitary M) (hvR : (v.support : H →L[ℂ] H)∈R)
    (hrest : 0<(τ (1-v.support)).re) (N : ℕ) {δ ζ : ℝ} (hδ : 0<δ) (hζ : 0<ζ) :
    ∃ w : PartialUnitary M, (w.val : H →L[ℂ] H)∈R ∧
      (w.support : H →L[ℂ] H)∈R ∧ w.support ≤ 1-v.support ∧
      v.support*w.support=0 ∧ 0<(τ w.support).re ∧ (τ w.support).re<ζ ∧
      (∀ i,‖τ (w.power (k i))‖ ≤ δ*(τ w.support).re) ∧
      (∀ (s : List (Letter J K)) (j : J),s.length ≤ N →
        TracialL2.norm τ (w.support*cornerCenter τ (1-v.support)
          (word x k v s*x j)*w.support)^2 ≤ δ^2*(τ w.support).re) ∧
      (∀ (s t : List (Letter J K)) (j : J) (i : K),s.length ≤ N → t.length ≤ N →
        ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ δ*(τ w.support).re) := by
  sorry

end Kadison.FinitePatching

end

end
end

end OAI
end
