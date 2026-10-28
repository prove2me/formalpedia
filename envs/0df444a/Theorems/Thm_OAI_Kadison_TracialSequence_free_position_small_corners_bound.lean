-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_free_position_small_corners_bound
-- name    : OAI.Kadison.TracialSequence.free_position_small_corners_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:02:23.309041+00:00
-- url     : https://prove2.me/theorems/76e3b955-0dfc-4ce0-b20f-8fb7844ae68f
-- title:
--   OAI.Kadison.TracialSequence.free_position_small_corners_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator`, `open Filter`, `open FreeWordTensor FreeWordAction FreeMoments FreeBlocks`):
--
--   ```lean
--   theorem free_position_small_corners_bound
--       (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
--       (T : τ.GNS →L[ℂ] τ.GNS)
--       (hTQ : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
--       {b c β : ℝ} (hb : 0≤b) (hc : 0 ≤ c) (hβ : 0<β) (hβ1 : β≤1) (hβb : β<b)
--       (hTC : ∀ q : Q,IsStarProjection q → (τ (j q)).re≤b →
--         ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖ ≤ c*‖a‖)
--       (s : unitary A) (hs0 : τ (s:A)=0) (hs2 : (s:A)*(s:A)=1) :
--       ‖T*τ.gnsStarAlgHom (s:A)-τ.gnsStarAlgHom (s:A)*T‖≤1040*c
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.FreeMoments.Free` and `OAI.Kadison.FreeWordTensor.FaithfulState` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.HilbertSequence.Pre` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.TracialSequence.constantSequence` and `OAI.Kadison.TracialSequence.mapSequence` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.HilbertSequence.instAddCommGroupPre` and `OAI.Kadison.HilbertSequence.instModuleComplexPre` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.instInnerProductSpaceComplexPre` and `OAI.Kadison.HilbertSequence.instSeminormedAddCommGroupPre` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.VectorGNS.inclusion` (definitions bundle `OAIQ039C060` of this split); `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.constantHom`, `OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace`, `OAI.Kadison.TracialSequence.leftRestricted`, `OAI.Kadison.TracialSequence.sequenceVacuum` and `OAI.Kadison.VectorGNS.GeneratedByStages` (definitions bundle `OAIQ039C064` of this split); `OAI.Kadison.TracialSequence.subalgebraState` (definitions bundle `OAIQ039C072` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.generated_free_small_corners_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C072

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

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open FreeWordTensor FreeWordAction FreeMoments FreeBlocks

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)

variable (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
  (hone : τ 1=1)
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)

variable (D : VonNeumannAlgebra (boundedSubspace τ ω))
  (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)

variable (R : Bool → StarSubalgebra ℂ M)
  (hR : R false=(VectorGNS.inclusion M D hDM).range)
  (hP : ∀ a : A,constantHom τ ω M hconst a∈R true)
  (hfree : Free R (subalgebraState τ ω hτ M hM hone).functional.toLinearMap)
  (hgen : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
    Set.centralizer (Set.centralizer (((iSup R).map M.toStarSubalgebra.subtype) : Set _)))

variable (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ},n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a,φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ Fintype.card (I m))

variable (hDgen : VectorGNS.GeneratedByStages D (sequenceVacuum τ ω) I φ)

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
  (hDQ : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
    Set.range ((leftRestricted τ ω).comp (mapSequence j)))

include hτ hω hM hone hconst hR hP hfree hgen hinc hsize hDgen hDQ in
theorem free_position_small_corners_bound
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
    (T : τ.GNS →L[ℂ] τ.GNS)
    (hTQ : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
    {b c β : ℝ} (hb : 0≤b) (hc : 0 ≤ c) (hβ : 0<β) (hβ1 : β≤1) (hβb : β<b)
    (hTC : ∀ q : Q,IsStarProjection q → (τ (j q)).re≤b →
      ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖ ≤ c*‖a‖)
    (s : unitary A) (hs0 : τ (s:A)=0) (hs2 : (s:A)*(s:A)=1) :
    ‖T*τ.gnsStarAlgHom (s:A)-τ.gnsStarAlgHom (s:A)*T‖≤1040*c := by
  sorry

end Kadison.TracialSequence

end

end
end

end OAI
end
