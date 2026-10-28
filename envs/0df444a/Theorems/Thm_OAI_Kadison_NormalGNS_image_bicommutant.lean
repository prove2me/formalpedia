-- Prove2me | Theorems.Thm_OAI_Kadison_NormalGNS_image_bicommutant
-- name    : OAI.Kadison.NormalGNS.image_bicommutant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:46:09.272338+00:00
-- url     : https://prove2.me/theorems/6fae65aa-4b88-4c9a-92c1-2a8de609e6c6
-- title:
--   OAI.Kadison.NormalGNS.image_bicommutant: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.NormalGNS`, with `open scoped InnerProductSpace Topology ComplexOrder`, `open Filter`):
--
--   ```lean
--   lemma image_bicommutant (a : M)
--       (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
--       τ.gnsStarAlgHom a∈N
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.MatrixTower.original_gns_generated`, `OAI.Kadison.NormalGNS.matrix_stages_gns` and `OAI.Kadison.VectorGNS.gns_generation` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
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

open scoped InnerProductSpace Topology ComplexOrder

open Filter

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hnormal : BoundedWOTContinuous M τ)
  (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
  (hSM : S≤M.toStarSubalgebra)
  (N : VonNeumannAlgebra τ.GNS)
  (hSN : ∀ a : M,(a:H →L[ℂ] H)∈S → τ.gnsStarAlgHom a∈N)

include hnormal hS hSM hSN in
lemma image_bicommutant (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    τ.gnsStarAlgHom a∈N := by
  sorry

end Kadison.NormalGNS

end

end
end

end OAI
end
