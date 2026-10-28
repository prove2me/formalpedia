-- Prove2me | Theorems.Thm_OAI_Kadison_FinitePatching_Words_momentBound_add
-- name    : OAI.Kadison.FinitePatching.Words.momentBound_add
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:53:06.470865+00:00
-- url     : https://prove2.me/theorems/0690018c-651d-4057-94e3-edf9aeee1ea4
-- title:
--   OAI.Kadison.FinitePatching.Words.momentBound_add: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FinitePatching.Words`, with `open scoped ComplexOrder`):
--
--   ```lean
--   theorem momentBound_add (hx : ∀ j,‖x j‖ ≤ 1)
--       (v w : PartialUnitary A) (horth : v.support*w.support=0)
--       (hqp : w.support ≤ 1-v.support) {N : ℕ} {ε η : ℝ}
--       (hε : 0 ≤ ε) (hη : 0<η) (hrest : η ≤ (τ (1-v.support)).re)
--       (hbound : MomentBound τ x k v N (momentBudget ε (budgetSlope N η) (τ v.support).re))
--       (hpure : ∀ i,‖τ (w.power (k i))‖ ≤ ε*(τ w.support).re)
--       (hsmall : ∀ (s : List (Letter J K)) (j : J),s.length ≤ N →
--         TracialL2.norm τ (w.support*cornerCenter τ (1-v.support) (word x k v s*x j)*w.support)^2 ≤
--           ε^2*(τ w.support).re)
--       (hphase : ∀ (s t : List (Letter J K)) (j : J) (i : K),s.length ≤ N → t.length ≤ N →
--         ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ ε*(τ w.support).re) :
--       MomentBound τ x k (v.add w horth) N
--         (momentBudget ε (budgetSlope N η) (τ (v.add w horth).support).re)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FinitePatching.PartialUnitary` and `OAI.Kadison.FinitePatching.PartialUnitary.power` (definitions bundle `OAIQ039C009` of this split); `OAI.Kadison.FinitePatching.budgetSlope`, `OAI.Kadison.FinitePatching.cornerCenter` and `OAI.Kadison.FinitePatching.momentBudget` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialL2.norm` (definitions bundle `OAIQ039C017` of this split); `OAI.Kadison.FinitePatching.Words.Letter` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FinitePatching.PartialUnitary.add`, `OAI.Kadison.FinitePatching.Words.MomentBound` and `OAI.Kadison.FinitePatching.Words.word` (definitions bundle `OAIQ039C035` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FinitePatching.exists_almost_full_finite_tests` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C017
import Definitions.Def_OAIQ039C035

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

variable (x : J → A) (k : K → ℤ)

include hτ in
theorem momentBound_add (hx : ∀ j,‖x j‖ ≤ 1)
    (v w : PartialUnitary A) (horth : v.support*w.support=0)
    (hqp : w.support ≤ 1-v.support) {N : ℕ} {ε η : ℝ}
    (hε : 0 ≤ ε) (hη : 0<η) (hrest : η ≤ (τ (1-v.support)).re)
    (hbound : MomentBound τ x k v N (momentBudget ε (budgetSlope N η) (τ v.support).re))
    (hpure : ∀ i,‖τ (w.power (k i))‖ ≤ ε*(τ w.support).re)
    (hsmall : ∀ (s : List (Letter J K)) (j : J),s.length ≤ N →
      TracialL2.norm τ (w.support*cornerCenter τ (1-v.support) (word x k v s*x j)*w.support)^2 ≤
        ε^2*(τ w.support).re)
    (hphase : ∀ (s t : List (Letter J K)) (j : J) (i : K),s.length ≤ N → t.length ≤ N →
      ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ ε*(τ w.support).re) :
    MomentBound τ x k (v.add w horth) N
      (momentBudget ε (budgetSlope N η) (τ (v.add w horth).support).re) := by
  sorry

end Kadison.FinitePatching.Words

end

end
end

end OAI
end
