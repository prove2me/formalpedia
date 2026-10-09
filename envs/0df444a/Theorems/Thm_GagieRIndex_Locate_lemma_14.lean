-- Prove2me | Theorems.Thm_GagieRIndex_Locate_lemma_14
-- name    : GagieRIndex.Locate.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:46.696934+00:00
-- url     : https://prove2.me/theorems/056fae2f-2216-4a86-b099-2e8110af70be
-- title:
--   Lemma 14, p. 23 — inside a phrase of ISA, φ is consecutive and preserves DISA
-- statement:
--   Let $T[1..n]$ be a text terminated by the unique smallest symbol $\$$, with suffix array $SA$, inverse suffix array $ISA$, the permutation $\phi$ of Definition 2, and the differential inverse suffix array $DISA$. A text position $i$ starts a phrase of $ISA$ when $ISA[i]$ is the first position of a BWT run. Let $2\le i\le n$ and suppose $[i-1..i]$ lies within a phrase of $ISA$, i.e. $i$ does not start a phrase of $ISA$. Then
--   $$\phi(i-1)=\phi(i)-1\qquad\text{and}\qquad DISA[i]=DISA[\phi(i)].$$
--
--   This is the analogue of Lemma 12 for the inverse suffix array, with $\phi$ playing the role of LF. Iterating it along a phrase shows that $\phi$ shifts whole phrases rigidly, which is the left half of the identity in the proof of Lemma 3.
--
--   **Formalization Note** "$[i-1..i]$ within a phrase of $ISA$" is encoded as "$i$ does not start a phrase of $ISA$", as in the paper's proof ("since $i$ is not a phrase beginning, $p$ is not the first position in a BWT run"). The phrases of $ISA$ start only at run-first positions, unlike the phrases of Definition 3.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 23, Lemma 14 (phrases of ISA defined on pp. 22–23)

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Phrases
import Definitions.Def_GagieRIndex_Locate_Arrays

namespace GagieRIndex.Locate

theorem lemma_14 (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : IsText n σ T) (hSA : IsSuffixArray n T SA)
    (i : ℕ) (hi2 : 2 ≤ i) (hin : i ≤ n)
    (hphrase : ¬ IsISAPhraseStart n T SA i) :
    phi n SA (i - 1) = phi n SA i - 1 ∧
      DISA n SA i = DISA n SA (phi n SA i) := by sorry

end GagieRIndex.Locate
