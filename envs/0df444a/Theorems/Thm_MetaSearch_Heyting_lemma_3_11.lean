-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_3_11
-- name    : MetaSearch.Heyting.lemma_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:50.159981+00:00
-- url     : https://prove2.me/theorems/8a0aff35-3de9-44f2-be39-c27e4a412bca
-- title:
--   Lemma 3.11 — the Heyting arrow of ideals: A → B = ⋂_{R∈A} ⋃_{S∈B} (↓R → ↓S), the class of problems reducing to refutations of reductions
-- statement:
--   Let $A,B$ be ideals of $\mathsf{Verifiable}$. Then the Heyting arrow $A\to B$ (the maximum ideal $C$ with $C\cap A\subseteq B$) exists and
--   $$A\to B=\bigcap_{R\in A}\ \bigcup_{S\in B}\ (\downarrow R\to\downarrow S),$$
--   where $\downarrow R\to\downarrow S$ is the Heyting arrow of the principal ideals. In other words, $A\to B$ is the set of verifiable search problems $T$ such that for each $R\in A$ there are $S\in B$ and $k\in\mathbb N$ with $T\le R\to_k S$.
--
--   Differences from the source:
--   - encoding: 'A → B … is equal to ⋂_{R∈A} ⋃_{S∈B} (↓R → ↓S)' → for every family H(R, S) of Heyting arrows ↓R → ↓S (R ∈ A, S ∈ B), `IsHeytingArrow A B (⋂ R ∈ A, ⋃ S ∈ B, H R S)`; and `IsHeytingArrow A B` of the set in the 'in other words' sentence; reason: Heyting arrows are given by maximality, so the principal arrows enter as any (necessarily unique) family having that property
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), p. 27, Lemma 3.11

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_3_11 (A B : Set SearchProblem) (hA : IsIdeal A) (hB : IsIdeal B) :
    -- `A → B = ⋂_{R ∈ A} ⋃_{S ∈ B} (↓R → ↓S)`, for the Heyting arrows `H R S = ↓R → ↓S`
    (∀ H : SearchProblem → SearchProblem → Set SearchProblem,
      (∀ R ∈ A, ∀ S ∈ B, IsHeytingArrow (down {R}) (down {S}) (H R S)) →
      IsHeytingArrow A B (⋂ R ∈ A, ⋃ S ∈ B, H R S)) ∧
    -- in other words: the verifiable `T` reducing, for each `R ∈ A`, to some `R →_k S`, `S ∈ B`
    IsHeytingArrow A B
      {T | T ∈ Verifiable ∧ ∀ R ∈ A, ∃ S ∈ B, ∃ k : ℕ, Reduces T (arrow k R S)} := by sorry

end MetaSearch.Heyting
