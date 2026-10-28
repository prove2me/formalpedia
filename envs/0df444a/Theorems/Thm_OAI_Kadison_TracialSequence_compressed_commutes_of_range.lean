-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_compressed_commutes_of_range
-- name    : OAI.Kadison.TracialSequence.compressed_commutes_of_range
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:43:48.670566+00:00
-- url     : https://prove2.me/theorems/1e2e2f44-d411-4816-a8c2-7544072b3258
-- title:
--   OAI.Kadison.TracialSequence.compressed_commutes_of_range: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped ComplexOrder`):
--
--   ```lean
--   lemma compressed_commutes_of_range (T : τ.GNS →L[ℂ] τ.GNS)
--       (hT : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
--       (d : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
--       (hd : d∈Set.range ((leftRestricted τ ω).comp (mapSequence j))) :
--       compressed τ ω T*d=d*compressed τ ω T
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertSequence.Pre` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.TracialSequence.mapSequence` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.HilbertSequence.instAddCommGroupPre` and `OAI.Kadison.HilbertSequence.instModuleComplexPre` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.instInnerProductSpaceComplexPre` and `OAI.Kadison.HilbertSequence.instSeminormedAddCommGroupPre` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.compressed`, `OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace` and `OAI.Kadison.TracialSequence.leftRestricted` (definitions bundle `OAIQ039C064` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.free_position_small_corners_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C064

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder

namespace Kadison.TracialSequence

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)

lemma compressed_commutes_of_range (T : τ.GNS →L[ℂ] τ.GNS)
    (hT : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
    (d : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
    (hd : d∈Set.range ((leftRestricted τ ω).comp (mapSequence j))) :
    compressed τ ω T*d=d*compressed τ ω T := by
  sorry

end Kadison.TracialSequence

end

end
end

end OAI
end
