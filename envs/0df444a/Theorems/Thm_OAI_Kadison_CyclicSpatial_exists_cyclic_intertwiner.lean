-- Prove2me | Theorems.Thm_OAI_Kadison_CyclicSpatial_exists_cyclic_intertwiner
-- name    : OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:33:45.710583+00:00
-- url     : https://prove2.me/theorems/2356977e-1576-43b9-a77f-48167a9ce549
-- title:
--   OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CyclicSpatial`, with `open scoped BigOperators InnerProductSpace`, `open CyclicColumns ReducingRepresentation`):
--
--   ```lean
--   theorem exists_cyclic_intertwiner (M : VonNeumannAlgebra H)
--       (hlam : Function.Injective lam) (hrange : Set.range lam=(M : Set (H →L[ℂ] H)))
--       (G : K →L[ℂ] H) (Ω : K)
--       (hΩ : DenseRange (fun a : A => restrict lam K hinv a Ω))
--       {c : ℝ} (hc : 0 ≤ c)
--       (hcol : ∀ (n : ℕ) (v : Fin n → A) (ζ : K),
--         ‖WithLp.toLp 2 (fun i => delta lam K hinv G (v i) ζ)‖ ≤ c*columnNorm v*‖ζ‖) :
--       ∃ T : K →L[ℂ] H, (∀ a : A,T.comp (restrict lam K hinv a)=(lam a).comp T) ∧
--         ‖G-T‖≤4*c
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CyclicColumns.columnNorm` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.CyclicSpatial.delta` and `OAI.Kadison.ReducingRepresentation.restrict` (definitions bundle `OAIQ039C005` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.CyclicSpatial.exists_embedded_cyclic_intertwiner` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C004
import Definitions.Def_OAIQ039C005

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

open scoped BigOperators InnerProductSpace

namespace Kadison.CyclicSpatial

open CyclicColumns ReducingRepresentation

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

attribute [local instance] OAI.Kadison.CyclicSpatial.instDecidableEq_solutions
variable (lam : A →⋆ₐ[ℂ] (H →L[ℂ] H))
  (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → lam a x∈K)

theorem exists_cyclic_intertwiner (M : VonNeumannAlgebra H)
    (hlam : Function.Injective lam) (hrange : Set.range lam=(M : Set (H →L[ℂ] H)))
    (G : K →L[ℂ] H) (Ω : K)
    (hΩ : DenseRange (fun a : A => restrict lam K hinv a Ω))
    {c : ℝ} (hc : 0 ≤ c)
    (hcol : ∀ (n : ℕ) (v : Fin n → A) (ζ : K),
      ‖WithLp.toLp 2 (fun i => delta lam K hinv G (v i) ζ)‖ ≤ c*columnNorm v*‖ζ‖) :
    ∃ T : K →L[ℂ] H, (∀ a : A,T.comp (restrict lam K hinv a)=(lam a).comp T) ∧
      ‖G-T‖≤4*c := by
  sorry

end Kadison.CyclicSpatial

end

end
end

end OAI
end
