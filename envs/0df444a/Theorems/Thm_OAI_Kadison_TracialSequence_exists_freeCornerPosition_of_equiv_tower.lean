-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_exists_freeCornerPosition_of_equiv_tower
-- name    : OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:56:12.999929+00:00
-- url     : https://prove2.me/theorems/bb3f4057-e89f-4a97-911b-821554fd6efe
-- title:
--   OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped ComplexOrder Matrix.Norms.L2Operator Topology`, `open Filter`, `open FinitePatching FinitePatching.ConjugatedWords`):
--
--   ```lean
--   theorem exists_freeCornerPosition_of_equiv_tower [TopologicalSpace.SeparableSpace σ.GNS]
--       (htrace : ∀ a,σ (e a)=τ a)
--       (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hσ : ∀ a b : M,σ (a*b)=σ (b*a))
--       (hω : (ω : Filter ℕ) ≤ atTop)
--       (hnormal : NormalGNS.BoundedWOTContinuous M σ)
--       (hfaith : ∀ a : M,σ (star a*a)=0 → a=0) (hone : τ 1=1)
--       (hirr : ∀ b : M,(∀ n (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ),
--         stage n a*b=b*stage n a) → ∃ c : ℂ,b=algebraMap ℂ M c)
--       (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
--       (hinc : ∀ n m (h : n ≤ m) a,stage m (inc h a)=stage n a)
--       (hgrow : Tendsto (fun n => (size n+1:ℝ)) atTop atTop)
--       (hdiffuse : DiffuseProjection.HasNoMinimalProjections R) :
--       Nonempty (FreeCornerPosition τ ω R j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.NormalSubalgebra.inclusion` and `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.TracialSequence.FreeCornerPosition` (definitions bundle `OAIQ039C067` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_stages` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C067

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.ConjugatedWords

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (e : A ≃⋆ₐ[ℂ] M) (j : R →⋆ₐ[ℂ] A)
    (hj : ∀ q,e (j q)=NormalSubalgebra.inclusion M R hRM q)

variable (τ : A →ₚ[ℂ] ℂ) (σ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] M)

variable (inc : ∀ {n m : ℕ},n ≤ m → Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ]
  Matrix (Fin (size m+1)) (Fin (size m+1)) ℂ)

include hRM hj in
theorem exists_freeCornerPosition_of_equiv_tower [TopologicalSpace.SeparableSpace σ.GNS]
    (htrace : ∀ a,σ (e a)=τ a)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hσ : ∀ a b : M,σ (a*b)=σ (b*a))
    (hω : (ω : Filter ℕ) ≤ atTop)
    (hnormal : NormalGNS.BoundedWOTContinuous M σ)
    (hfaith : ∀ a : M,σ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ),
      stage n a*b=b*stage n a) → ∃ c : ℂ,b=algebraMap ℂ M c)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hinc : ∀ n m (h : n ≤ m) a,stage m (inc h a)=stage n a)
    (hgrow : Tendsto (fun n => (size n+1:ℝ)) atTop atTop)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R) :
    Nonempty (FreeCornerPosition τ ω R j) := by
  sorry

end Kadison.TracialSequence

end

end
end

end OAI
end
