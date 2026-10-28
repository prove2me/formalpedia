-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_freeCornerPosition_of_unitary_abstract
-- name    : OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:56:53.620009+00:00
-- url     : https://prove2.me/theorems/db29ee76-fa89-46ee-92d2-578f45da0cd3
-- title:
--   OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator`, `open Filter`, `open FinitePatching.ConjugatedWords`):
--
--   ```lean
--   theorem freeCornerPosition_of_unitary_abstract
--       (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)
--       (hconstantclosed : Set.centralizer (Set.centralizer (Set.range (constantAction τ ω)))=
--         Set.range (constantAction τ ω))
--       (hfaith : ∀ a : A,τ (star a*a)=0 → a=0) (hone : τ 1=1)
--       (hirr : ∀ b : A,(∀ n (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ),
--         stage n a*b=b*stage n a) → ∃ c : ℂ,b=algebraMap ℂ A c)
--       (hstage : ∀ n a,stage n a∈Set.range j)
--       (hinc : ∀ n m (h : n ≤ m) a,stage m (inc h a)=stage n a)
--       (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ size m+1)
--       (U : unitary (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω))
--       (hu : (U:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
--         Set.range ((leftRestricted τ ω).comp (mapSequence j)))
--       (hfree : FreeMoments.Free (pair (A := A) (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) (constantAction τ ω) U) (sequenceTrace τ ω).toLinearMap) :
--       Nonempty (FreeCornerPosition τ ω R j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FreeMoments.Free` and `OAI.Kadison.FinitePatching.ConjugatedWords.pair` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.HilbertSequence.Pre` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.TracialSequence.mapSequence` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.HilbertSequence.instAddCommGroupPre` and `OAI.Kadison.HilbertSequence.instModuleComplexPre` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.instInnerProductSpaceComplexPre` and `OAI.Kadison.HilbertSequence.instSeminormedAddCommGroupPre` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace` and `OAI.Kadison.TracialSequence.leftRestricted` (definitions bundle `OAIQ039C064` of this split); `OAI.Kadison.TracialSequence.FreeCornerPosition` and `OAI.Kadison.TracialSequence.constantAction` (definitions bundle `OAIQ039C067` of this split); `OAI.Kadison.TracialSequence.sequenceTrace` (definitions bundle `OAIQ039C069` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C069

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open FinitePatching.ConjugatedWords

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (R : VonNeumannAlgebra H) (j : R →⋆ₐ[ℂ] A)

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] A)

variable (inc : ∀ {n m : ℕ},n ≤ m → Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ]
  Matrix (Fin (size m+1)) (Fin (size m+1)) ℂ)

theorem freeCornerPosition_of_unitary_abstract
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)
    (hconstantclosed : Set.centralizer (Set.centralizer (Set.range (constantAction τ ω)))=
      Set.range (constantAction τ ω))
    (hfaith : ∀ a : A,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : A,(∀ n (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ),
      stage n a*b=b*stage n a) → ∃ c : ℂ,b=algebraMap ℂ A c)
    (hstage : ∀ n a,stage n a∈Set.range j)
    (hinc : ∀ n m (h : n ≤ m) a,stage m (inc h a)=stage n a)
    (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ size m+1)
    (U : unitary (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω))
    (hu : (U:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)))
    (hfree : FreeMoments.Free (pair (A := A) (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) (constantAction τ ω) U) (sequenceTrace τ ω).toLinearMap) :
    Nonempty (FreeCornerPosition τ ω R j) := by
  sorry

end Kadison.TracialSequence

end

end OAI
end
