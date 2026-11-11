-- Prove2me | Theorems.Thm_MetaSearch_Heyting_theorem_1_4
-- name    : MetaSearch.Heyting.theorem_1_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:31.978195+00:00
-- url     : https://prove2.me/theorems/499c6463-8ea9-484f-8a7f-a1e8515b6c62
-- title:
--   Theorem 1.4 — the complexity classes of verifiable search problems form a complete Heyting algebra whose negations and arrows are refutation classes
-- statement:
--   Call a **complexity class** an ideal of $(\mathsf{Verifiable},\le)$, where $\le$ is mapping reducibility: a nonempty set of verifiable search problems, downward closed under reductions within $\mathsf{Verifiable}$, and closed under finite joins $\vee$. Ordered by $\subseteq$ they form a complete Heyting algebra: there is a frame structure on the ideals with order $\subseteq$, bottom $\mathsf{FP}$, top $\mathsf{Verifiable}$, meet $\cap$, and negation and arrow given by (5) and (6). Moreover:
--
--   0. $I$ is an ideal iff $I\subseteq\mathsf{Verifiable}$, $I\ne\emptyset$, $I$ is downward closed within $\mathsf{Verifiable}$, and $I$ is closed under finite joins (empty join $\mathsf{triv}$);
--   1. $\mathsf{FP}$ is an ideal contained in every ideal;
--   2. $\mathsf{Verifiable}$ is an ideal containing every ideal;
--   3. for every nonempty family of ideals, its intersection is an ideal and the greatest ideal below all of them;
--   4. for every family $\mathcal A$ of ideals, $\downarrow\{\text{finite }\vee\text{-joins of members of }\textstyle\bigcup\mathcal A\}$ is an ideal and the least ideal above all of them;
--   5. for every ideal $A$, the Heyting negation $\neg A$ (the largest ideal $C$ with $C\cap A\subseteq\mathsf{FP}$) is
--   $$\neg A=\{R\in\mathsf{Verifiable}:\forall S\in A\ \exists k\ \ R\le\neg_k S\};$$
--   6. for all ideals $A,B$, the Heyting arrow $A\to B$ (the largest ideal $C$ with $C\cap A\subseteq B$) is
--   $$A\to B=\{T\in\mathsf{Verifiable}:\forall R\in A\ \exists S\in B\ \exists k\ \ T\le R\to_k S\};$$
--   7. for $R,S\in\mathsf{Verifiable}$:
--   $$\downarrow R\cap\downarrow S=\downarrow(R\wedge S),\quad \downarrow R\vee\downarrow S=\downarrow(R\vee S),\quad \neg\downarrow S=\downarrow\{\neg_k S\}_k,\quad \downarrow R\to\downarrow S=\downarrow\{R\to_k S\}_k.$$
--
--   Here $\neg_k S$ is the task of refuting an $O(n^k)$-time algorithm for $S$ and $R\to_k S$ the task of refuting an $O(n^k)$-time reduction from $R$ to $S$. The theorem says that the Heyting operations of the lattice of complexity classes are the metacomplexity refutation tasks.
--
--   Differences from the source:
--   - reading: clauses 5 and 6: 'all search problems R' / 'all search problems T' → R ∈ Verifiable / T ∈ Verifiable; reason: literally false (INSIGHTS.yaml I1); Lemma 3.11 (p. 27) states 'all verifiable search problems', and classes are ideals of Verifiable
--   - encoding: 'The ideal completion of Verifiable … is a complete Heyting algebra', 'the meet/join of two classes … generalizes to infinite meets/joins', Heyting negation and arrow → existence of an `Order.Frame` on `IdealClass` with ≤ = ⊆ and the stated ⊥, ⊤, ⊓, ᶜ, ⇨ carriers; clauses (3)-(6) as set-level statements (intersection of a nonempty family; downward closure of `JoinClosure` of the union, the empty join triv; `IsHeytingArrow` maximality); reason: these are the meanings of the lattice operations of the ideal completion; the empty meet is clause 2 and the empty join is FP
--   - encoding: clause 7: '(↓R) ∨ (↓S) = ↓(R ∨ S)' and 'in the special case where the classes have complete problems R and S' → R, S ∈ Verifiable, and ↓(R ∨ S) is an ideal containing ↓R and ↓S and contained in every ideal containing both; reason: a class with complete problem R is ↓R; the join of ideals is their least upper bound
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), p. 8, Theorem 1.4 (derived on p. 28)

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem theorem_1_4 :
    -- the ideal completion is a complete Heyting algebra (a frame) under `⊆`,
    -- with bottom `FP`, top `Verifiable`, and arrows and negations the refutation classes
    (∃ _ : Order.Frame IdealClass,
      (∀ I J : IdealClass, I ≤ J ↔ I.carrier ⊆ J.carrier) ∧
      (⊥ : IdealClass).carrier = FP ∧ (⊤ : IdealClass).carrier = Verifiable ∧
      (∀ A B : IdealClass, (A ⊓ B).carrier = A.carrier ∩ B.carrier) ∧
      (∀ A : IdealClass, (Aᶜ).carrier =
        {R | R ∈ Verifiable ∧ ∀ S ∈ A.carrier, ∃ k : ℕ, Reduces R (neg k S)}) ∧
      (∀ A B : IdealClass, (A ⇨ B).carrier =
        {T | T ∈ Verifiable ∧ ∀ R ∈ A.carrier, ∃ S ∈ B.carrier, ∃ k : ℕ,
          Reduces T (arrow k R S)})) ∧
    -- (0) ideals are the complexity classes
    (∀ I : Set SearchProblem, IsIdeal I ↔
      (I ⊆ Verifiable ∧ I.Nonempty ∧
        (∀ R S, R ∈ Verifiable → Reduces R S → S ∈ I → R ∈ I) ∧
        ∀ S, JoinClosure I S → S ∈ I)) ∧
    -- (1) bottom `FP`
    (IsIdeal FP ∧ ∀ I, IsIdeal I → FP ⊆ I) ∧
    -- (2) top `Verifiable`
    (IsIdeal Verifiable ∧ ∀ I, IsIdeal I → I ⊆ Verifiable) ∧
    -- (3) meets of nonempty families are intersections
    (∀ 𝒜 : Set (Set SearchProblem), 𝒜.Nonempty → (∀ A ∈ 𝒜, IsIdeal A) →
      IsIdeal (⋂₀ 𝒜) ∧ (∀ A ∈ 𝒜, ⋂₀ 𝒜 ⊆ A) ∧
      ∀ C, IsIdeal C → (∀ A ∈ 𝒜, C ⊆ A) → C ⊆ ⋂₀ 𝒜) ∧
    -- (4) joins of families: downward closure of the finite `∨`-joins of the union
    (∀ 𝒜 : Set (Set SearchProblem), (∀ A ∈ 𝒜, IsIdeal A) →
      IsIdeal (down {S | JoinClosure (⋃₀ 𝒜) S}) ∧
      (∀ A ∈ 𝒜, A ⊆ down {S | JoinClosure (⋃₀ 𝒜) S}) ∧
      ∀ C, IsIdeal C → (∀ A ∈ 𝒜, A ⊆ C) → down {S | JoinClosure (⋃₀ 𝒜) S} ⊆ C) ∧
    -- (5) Heyting negation
    (∀ A, IsIdeal A → IsHeytingArrow A FP
      {R | R ∈ Verifiable ∧ ∀ S ∈ A, ∃ k : ℕ, Reduces R (neg k S)}) ∧
    -- (6) Heyting arrow
    (∀ A B, IsIdeal A → IsIdeal B → IsHeytingArrow A B
      {T | T ∈ Verifiable ∧ ∀ R ∈ A, ∃ S ∈ B, ∃ k : ℕ, Reduces T (arrow k R S)}) ∧
    -- (7) classes with complete problems
    (∀ R ∈ Verifiable, ∀ S ∈ Verifiable,
      down {R} ∩ down {S} = down {meet R S} ∧
      (IsIdeal (down {join R S}) ∧ down {R} ⊆ down {join R S} ∧ down {S} ⊆ down {join R S} ∧
        ∀ C, IsIdeal C → down {R} ⊆ C → down {S} ⊆ C → down {join R S} ⊆ C) ∧
      IsHeytingArrow (down {S}) FP (down (Set.range fun k : ℕ => neg k S)) ∧
      IsHeytingArrow (down {R}) (down {S}) (down (Set.range fun k : ℕ => arrow k R S))) := by sorry

end MetaSearch.Heyting
