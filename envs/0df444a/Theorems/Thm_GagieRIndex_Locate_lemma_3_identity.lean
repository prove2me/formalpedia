-- Prove2me | Theorems.Thm_GagieRIndex_Locate_lemma_3_identity
-- name    : GagieRIndex.Locate.lemma_3_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:30.313222+00:00
-- url     : https://prove2.me/theorems/57b1927c-7bc8-4cb6-bb29-735f986dd07d
-- title:
--   Proof of Lemma 3, pp. 12–13 — SA[p − 1] = x + k − i and SA[p + 1] = y + k − i from the sample N[i] = ⟨x, y⟩
-- statement:
--   Let $T[1..n]$ be a text terminated by the unique smallest symbol $\$$, with suffix array $SA$ and inverse suffix array $ISA$. Fix a suffix-array position $1\le p\le n$ and write $SA[p]=k+1$, so that $BWT[p]=T[k]$. Let $i$ be the position of the first character of the phrase containing $T[k]$ (Definition 3), i.e. the greatest sampled position $\le k$, and let $q=ISA[i+1]$ be the cell with $SA[q]=i+1$, so that $BWT[q]=T[i]$. The sample stored for $i$ is $N[i]=\langle x,y\rangle=\langle SA[q-1],SA[q+1]\rangle$. Then:
--
--   1. if $p\ge 2$, then $q\ge 2$ and $SA[p-1]=x+k-i$;
--   2. if $p<n$, then $q<n$ and $SA[p+1]=y+k-i$.
--
--   In display form,
--   $$SA[p-1]=SA[q-1]+(k-i),\qquad SA[p+1]=SA[q+1]+(k-i).$$
--
--   Hence the two neighbouring suffix-array cells of any known cell are recovered from the samples $N[\cdot]$ stored at the $O(r)$ phrase starts, by one predecessor search. Starting from the toehold of Lemma 2, this lists the whole interval $SA[sp..ep]$ of a pattern's occurrences. This identity is the correctness content of Lemma 3 and of the locating half of Theorem 1.
--
--   **Formalization Note** If no sampled position is $\le k$, the phrase containing $T[k]$ wraps around through $T[n]=\$$ (which is always sampled); the phrase head is then $0$, read as $T[0]\equiv T[n]$ as in the definition of the BWT, and $q=ISA[1]$ is the cell holding $\$$. The identity covers this case unchanged. The conclusions $q\ge 2$ and $q<n$ say that $N[i]$ is defined. The case $SA[p]=1$ ($k=i=0$, $q=p$) is included. The paper's $O(\cdot)$ space and time claims are not part of the statement.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, pp. 12–13, proof of Lemma 3 (first, second and last paragraphs)

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Phrases

namespace GagieRIndex.Locate

theorem lemma_3_identity (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : IsText n σ T) (hSA : IsSuffixArray n T SA)
    (p : ℕ) (hp1 : 1 ≤ p) (hpn : p ≤ n) :
    let k := SA p - 1
    let i := phraseHead n T SA k
    let q := ISA n SA (i + 1)
    (2 ≤ p → 2 ≤ q ∧ SA (p - 1) = SA (q - 1) + (k - i)) ∧
    (p < n → q < n ∧ SA (p + 1) = SA (q + 1) + (k - i)) := by sorry

end GagieRIndex.Locate
