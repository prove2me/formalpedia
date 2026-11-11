-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_3_10
-- name    : MetaSearch.Heyting.lemma_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:43.922696+00:00
-- url     : https://prove2.me/theorems/b7ecc830-59c7-42d2-8c1b-f62fa38318d4
-- title:
--   Lemma 3.10 — the Heyting arrow of principal ideals: ↓R → ↓S = ↓{R →_k S : k ∈ ℕ}
-- statement:
--   For $R,S\in\mathsf{Verifiable}$, the set
--   $$\downarrow\{R\to_k S: k\in\mathbb N\}=\{T\in\mathsf{Verifiable}: T\le R\to_k S\text{ for some }k\}$$
--   is the Heyting arrow $\downarrow R\to\downarrow S$: it is an ideal, its intersection with $\downarrow R$ lies in $\downarrow S$, and it contains every ideal $C$ with $C\cap\downarrow R\subseteq\downarrow S$.
--
--   Differences from the source:
--   - encoding: '↓R → ↓S = ↓{R →_k S : k ∈ ℕ}', with A → B defined (p. 26) as the maximum ideal C with C ∩ A ⊆ B → `IsHeytingArrow (down {R}) (down {S}) (down (Set.range fun k => arrow k R S))`; reason: the arrow is defined as a maximum, so equality with it means being that maximum
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), p. 27, Lemma 3.10

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_3_10 (R S : SearchProblem) (hR : R ∈ Verifiable) (hS : S ∈ Verifiable) :
    IsHeytingArrow (down {R}) (down {S}) (down (Set.range fun k : ℕ => arrow k R S)) := by sorry

end MetaSearch.Heyting
