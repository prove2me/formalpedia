-- Prove2me | Theorems.Thm_OAI_Kadison_FinitePatching_Words_word_perturbation_bound
-- name    : OAI.Kadison.FinitePatching.Words.word_perturbation_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:53:34.563722+00:00
-- url     : https://prove2.me/theorems/430102eb-b34f-4d29-9a0b-8fd82c690ca2
-- title:
--   OAI.Kadison.FinitePatching.Words.word_perturbation_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FinitePatching.Words`, with `open scoped ComplexOrder`):
--
--   ```lean
--   theorem word_perturbation_bound (hx : ∀ j,‖x j‖ ≤ 1)
--       (v w : PartialUnitary A) (horth : v.support*w.support=0)
--       (hqp : w.support ≤ 1-v.support) {N : ℕ} {B δ η : ℝ}
--       (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hη : 0<η) (hrest : η ≤ (τ (1-v.support)).re)
--       (hbound : MomentBound τ x k v N B)
--       (hsmall : ∀ (s : List (Letter J K)) (j : J), s.length ≤ N →
--         TracialL2.norm τ (w.support*cornerCenter τ (1-v.support) (word x k v s*x j)*w.support)^2 ≤
--           δ^2*(τ w.support).re)
--       (hphase : ∀ (s t : List (Letter J K)) (j : J) (i : K),
--         s.length ≤ N → t.length ≤ N →
--         ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ δ*(τ w.support).re)
--       (l : List (Letter J K)) (hlen : l.length ≤ N) (hv : Valid l) :
--       ‖τ (word x k (v.add w horth) l)-τ (word x k v l)‖ ≤
--         ((l.length:ℝ)+(l.length:ℝ)^2)*(δ+2*B/η)*(τ w.support).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FinitePatching.PartialUnitary` and `OAI.Kadison.FinitePatching.PartialUnitary.power` (definitions bundle `OAIQ039C009` of this split); `OAI.Kadison.FinitePatching.cornerCenter` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialL2.norm` (definitions bundle `OAIQ039C017` of this split); `OAI.Kadison.FinitePatching.Words.Letter` and `OAI.Kadison.FinitePatching.Words.Valid` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FinitePatching.PartialUnitary.add`, `OAI.Kadison.FinitePatching.Words.MomentBound` and `OAI.Kadison.FinitePatching.Words.word` (definitions bundle `OAIQ039C035` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FinitePatching.Words.momentBound_add` of this split imports it.
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

namespace Kadison.FinitePatching

namespace Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

variable (x : J → A) (k : K → ℤ)

include hτ in
theorem word_perturbation_bound (hx : ∀ j,‖x j‖ ≤ 1)
    (v w : PartialUnitary A) (horth : v.support*w.support=0)
    (hqp : w.support ≤ 1-v.support) {N : ℕ} {B δ η : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hη : 0<η) (hrest : η ≤ (τ (1-v.support)).re)
    (hbound : MomentBound τ x k v N B)
    (hsmall : ∀ (s : List (Letter J K)) (j : J), s.length ≤ N →
      TracialL2.norm τ (w.support*cornerCenter τ (1-v.support) (word x k v s*x j)*w.support)^2 ≤
        δ^2*(τ w.support).re)
    (hphase : ∀ (s t : List (Letter J K)) (j : J) (i : K),
      s.length ≤ N → t.length ≤ N →
      ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ δ*(τ w.support).re)
    (l : List (Letter J K)) (hlen : l.length ≤ N) (hv : Valid l) :
    ‖τ (word x k (v.add w horth) l)-τ (word x k v l)‖ ≤
      ((l.length:ℝ)+(l.length:ℝ)^2)*(δ+2*B/η)*(τ w.support).re := by
  sorry

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end
