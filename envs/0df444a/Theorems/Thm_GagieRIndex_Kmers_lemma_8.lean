-- Prove2me | Theorems.Thm_GagieRIndex_Kmers_lemma_8
-- name    : GagieRIndex.Kmers.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:42.720651+00:00
-- url     : https://prove2.me/theorems/201c0f25-db8e-4e83-8847-6b70495ad1f7
-- title:
--   Lemma 8, p. 17 — every text substring has a primary occurrence
-- statement:
--   Let $T[1..n]$ be a terminated text with suffix array $SA$. Every nonempty substring $T[i..j]$, where $1\le i\le j\le n$, has an equal-length occurrence $T[i'..j']$ that contains a sampled character:
--   $$\forall\,1\le i\le j\le n,\quad\exists\,1\le i'\le j'\le n:\ T[i'..j']=T[i..j]\ \text{and}\ \exists x\in\operatorname{Sampled}(T),\ i'\le x\le j'.$$
--
--   This primary-occurrence property is what lets the distinct-substring count focus on neighborhoods of run-boundary samples.
--
--   **Formalization Note** Equality of the two substrings is expressed pointwise at every offset from $0$ through $j-i$, and $j'=i'+(j-i)$. The bounds require a nonempty substring and keep the second occurrence inside $T$.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 17, Lemma 8; p. 16, Definition 5

import Mathlib
import Definitions.Def_GagieRIndex_Kmers_Smers

namespace GagieRIndex.Kmers

theorem lemma_8 (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n) :
    ∃ i', IsPrimary n T SA i' (i' + (j - i)) ∧
      ∀ t ≤ j - i, T (i' + t) = T (i + t) := by sorry

end GagieRIndex.Kmers
