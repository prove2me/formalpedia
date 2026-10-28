-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_represented_corner_bound
-- name    : OAI.Kadison.TracialSequence.represented_corner_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:46:31.871373+00:00
-- url     : https://prove2.me/theorems/a65d08fe-c0dd-4c18-88b1-d613682b9be3
-- title:
--   OAI.Kadison.TracialSequence.represented_corner_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped InnerProductSpace ComplexOrder`, `open Filter`):
--
--   ```lean
--   lemma represented_corner_bound (T : τ.GNS →L[ℂ] τ.GNS)
--       {b c β : ℝ} (hb : 0≤b) (hc : 0 ≤ c) (hβ : β<b)
--       (hT : ∀ q : Q,IsStarProjection q → (τ (j q)).re≤b →
--         ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖ ≤ c*‖a‖) :
--       VectorGNS.RepresentedCornerBound M (sequenceVacuum τ ω) D (compressed τ ω T) c (β:ℂ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertSequence.Pre` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.TracialSequence.mapSequence` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.HilbertSequence.instAddCommGroupPre` and `OAI.Kadison.HilbertSequence.instModuleComplexPre` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.instInnerProductSpaceComplexPre` and `OAI.Kadison.HilbertSequence.instSeminormedAddCommGroupPre` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.compressed`, `OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace`, `OAI.Kadison.TracialSequence.leftRestricted` and `OAI.Kadison.TracialSequence.sequenceVacuum` (definitions bundle `OAIQ039C064` of this split); `OAI.Kadison.VectorGNS.RepresentedCornerBound` (definitions bundle `OAIQ039C065` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.free_position_small_corners_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C064
import Definitions.Def_OAIQ039C065

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

open scoped InnerProductSpace ComplexOrder

open Filter

namespace Kadison.TracialSequence

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)

variable (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))

variable (D : VonNeumannAlgebra (boundedSubspace τ ω))

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
  (hDQ : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
    Set.range ((leftRestricted τ ω).comp (mapSequence j)))

include hτ hω hM hDQ in
lemma represented_corner_bound (T : τ.GNS →L[ℂ] τ.GNS)
    {b c β : ℝ} (hb : 0≤b) (hc : 0 ≤ c) (hβ : β<b)
    (hT : ∀ q : Q,IsStarProjection q → (τ (j q)).re≤b →
      ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖ ≤ c*‖a‖) :
    VectorGNS.RepresentedCornerBound M (sequenceVacuum τ ω) D (compressed τ ω T) c (β:ℂ) := by
  sorry

end Kadison.TracialSequence

end

end
end

end OAI
end
