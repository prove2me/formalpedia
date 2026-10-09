-- Prove2me | Theorems.Thm_GagieRIndex_Locate_run_free
-- name    : GagieRIndex.Locate.run_free
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:53.8197+00:00
-- url     : https://prove2.me/theorems/8eeb269c-3f35-4502-8580-f98e4df2c79a
-- title:
--   Proof of Lemma 3, pp. 12–13 — between T[k] and its phrase head, LF keeps p − 1, p, p + 1 contiguous in one run
-- statement:
--   Let $T[1..n]$ be a text terminated by the unique smallest symbol $\$$, with suffix array $SA$, Burrows–Wheeler transform $BWT$ and LF mapping $LF$. Fix a position $1\le p\le n$, write $SA[p]=k+1$ (so $BWT[p]=T[k]$), and let $i$ be the phrase head of $T[k]$, the greatest sampled position $\le k$ (or $0$). Then for every $0\le t<k-i$:
--
--   1. if $p\ge 2$, then $LF^t(p-1)+1=LF^t(p)$ and $BWT[LF^t(p-1)]=BWT[LF^t(p)]$;
--   2. if $p<n$, then $LF^t(p+1)=LF^t(p)+1$ and $BWT[LF^t(p+1)]=BWT[LF^t(p)]$.
--
--   That is,
--   $$LF^t(p-1),\ LF^t(p),\ LF^t(p+1)\ \text{are contiguous and within a single BWT run for all }0\le t<k-i.$$
--
--   Because none of $T[k],T[k-1],\dots,T[i+1]$ is the first or last character of its BWT run, the three neighbouring cells travel together under LF until the phrase head is reached. This is the core step of the correctness argument of Lemma 3.
--
--   **Formalization Note** $LF^t$ is the $t$-fold iterate of the LF mapping. Each neighbour is guarded by its existence ($p\ge 2$, $p<n$), which the page leaves implicit. The phrase head $0$ encodes a phrase that wraps around through $T[n]=\$$.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, pp. 12–13, proof of Lemma 3, third paragraph

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Phrases

namespace GagieRIndex.Locate

theorem run_free (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : IsText n σ T) (hSA : IsSuffixArray n T SA)
    (p : ℕ) (hp1 : 1 ≤ p) (hpn : p ≤ n) :
    let k := SA p - 1
    let i := phraseHead n T SA k
    ∀ t < k - i,
      (2 ≤ p → (LF n T SA)^[t] (p - 1) + 1 = (LF n T SA)^[t] p ∧
          bwt n T SA ((LF n T SA)^[t] (p - 1)) = bwt n T SA ((LF n T SA)^[t] p)) ∧
      (p < n → (LF n T SA)^[t] (p + 1) = (LF n T SA)^[t] p + 1 ∧
          bwt n T SA ((LF n T SA)^[t] (p + 1)) = bwt n T SA ((LF n T SA)^[t] p)) := by sorry

end GagieRIndex.Locate
