-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_2_14
-- name    : MetaSearch.Heyting.lemma_2_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:34.787026+00:00
-- url     : https://prove2.me/theorems/e79c198e-e1cf-475c-baa8-dd35476d39af
-- title:
--   Lemma 2.14 — distributivity R ∧ (S ∨ T) ≤ (R ∧ S) ∨ (R ∧ T); Search and Verifiable are distributive bounded preorder lattices
-- statement:
--   For all search problems $R,S,T$,
--   $$R\wedge(S\vee T)\;\le\;(R\wedge S)\vee(R\wedge T).$$
--   In particular $\mathsf{Search}$ and $\mathsf{Verifiable}$ are distributive bounded preorder lattices under $\le$: $\le$ is reflexive and transitive; $\mathsf{triv}\le S\le\mathsf{imp}$ for every $S$; $S_0\vee S_1$ is a least upper bound and $S_0\wedge S_1$ a greatest lower bound of $S_0,S_1$; and $\mathsf{Verifiable}$ contains $\mathsf{triv}$ and $\mathsf{imp}$ and is closed under $\vee$ and $\wedge$. (The reverse inequality $(R\wedge S)\vee(R\wedge T)\le R\wedge(S\vee T)$ holds in every preorder lattice.)
--
--   Differences from the source:
--   - reading: 'In particular, Verifiable and Search are distributive bounded preorder lattices under ≤' → stated as explicit conjuncts: ≤ reflexive and transitive, triv ≤ S ≤ imp, ∨ a least upper bound, ∧ a greatest lower bound, triv, imp ∈ Verifiable, Verifiable closed under ∨ and ∧; reason: this is what a distributive bounded preorder lattice means for these operations; the bounds are triv and imp (p. 17)
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), p. 19, Lemma 2.14

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_2_14 :
    -- distributivity
    (∀ R S T : SearchProblem, Reduces (meet R (join S T)) (join (meet R S) (meet R T))) ∧
    -- in particular: `≤` is a preorder on `Search` ...
    (∀ S : SearchProblem, Reduces S S) ∧
    (∀ R S T : SearchProblem, Reduces R S → Reduces S T → Reduces R T) ∧
    -- ... bounded by `triv` and `imp` ...
    (∀ S : SearchProblem, Reduces triv S ∧ Reduces S imp) ∧
    -- ... with joins `∨` and meets `∧` ...
    (∀ S₀ S₁ : SearchProblem, Reduces S₀ (join S₀ S₁) ∧ Reduces S₁ (join S₀ S₁) ∧
      ∀ T, Reduces S₀ T → Reduces S₁ T → Reduces (join S₀ S₁) T) ∧
    (∀ S₀ S₁ : SearchProblem, Reduces (meet S₀ S₁) S₀ ∧ Reduces (meet S₀ S₁) S₁ ∧
      ∀ R, Reduces R S₀ → Reduces R S₁ → Reduces R (meet S₀ S₁)) ∧
    -- ... and `Verifiable` contains the bounds and is closed under `∨` and `∧`
    triv ∈ Verifiable ∧ imp ∈ Verifiable ∧
    (∀ S₀ ∈ Verifiable, ∀ S₁ ∈ Verifiable, join S₀ S₁ ∈ Verifiable ∧ meet S₀ S₁ ∈ Verifiable) := by sorry

end MetaSearch.Heyting
