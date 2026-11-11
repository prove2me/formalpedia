-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_3_12
-- name    : MetaSearch.Heyting.lemma_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:42.635699+00:00
-- url     : https://prove2.me/theorems/7671e2e0-59e9-419a-ac60-1cd0bab6f42c
-- title:
--   Lemma 3.12 — Heyting negation: ¬↓R = ↓{¬_k R : k ∈ ℕ}, and ¬C = ⋂_{R∈C} ¬↓R
-- statement:
--   For $R\in\mathsf{Verifiable}$, the set $\downarrow\{\neg_k R:k\in\mathbb N\}$ is the Heyting negation $\neg\downarrow R=\downarrow R\to\mathsf{FP}$: it is an ideal meeting $\downarrow R$ inside $\mathsf{FP}$ and containing every ideal that does. Moreover, for every ideal $C$ of $\mathsf{Verifiable}$,
--   $$\neg C=\bigcap_{R\in C}\neg\downarrow R.$$
--
--   Differences from the source:
--   - encoding: '¬↓R = ↓{¬_kR : k ∈ ℕ}' and '¬C = ⋂_{R∈C} ¬↓R', with ¬A = A → FP the maximum ideal C with C ∩ A ⊆ FP (p. 26) → `IsHeytingArrow (down {R}) FP (down (Set.range fun k => neg k R))`; for every family N(R) of Heyting negations of ↓R (R ∈ C), `IsHeytingArrow C FP (⋂ R ∈ C, N R)`; reason: negations are given by maximality, so equality with one means being that maximum
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), pp. 27-28, Lemma 3.12

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_3_12 :
    (∀ R ∈ Verifiable,
      IsHeytingArrow (down {R}) FP (down (Set.range fun k : ℕ => neg k R))) ∧
    (∀ C : Set SearchProblem, IsIdeal C →
      ∀ N : SearchProblem → Set SearchProblem,
        (∀ R ∈ C, IsHeytingArrow (down {R}) FP (N R)) →
        IsHeytingArrow C FP (⋂ R ∈ C, N R)) := by sorry

end MetaSearch.Heyting
