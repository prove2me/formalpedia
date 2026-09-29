-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_initial_dense_prefix
-- name    : FranklKupavskii2022.EMC.initial_dense_prefix
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:16:35.436565+00:00
-- url     : https://prove2.me/theorems/c44cdcb6-1996-44f0-835b-34cef982ccca
-- title:
--   Proposition 4: members of an initial family with $\nu\le s$ meet some prefix densely
-- statement:
--   Let $k,s\ge1$ and let $\mathcal F\subseteq\binom{[m]}{k}$ be initial with $\nu(\mathcal F)\le s$. Then
--
--   $$
--   \{s+1,\,2(s+1),\,\dots,\,k(s+1)\}\notin\mathcal F,
--   $$
--
--   and consequently for every $F\in\mathcal F$ there is some $i$ with $1\le i\le k$ and
--
--   $$
--   |F\cap[i(s+1)-1]|\ge i. \tag{10}
--   $$
--
--   This structural fact about shifted families is the starting point of the analysis of shadows in Section 2.1.
--
--   **Formalization Note** The Sect. 1 standing assumption that $k$ and $s$ are positive integers is included; for $k=0$ the first claim fails for $\mathcal F=\{\emptyset\}$.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Proposition 4, p. 4

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial

namespace FranklKupavskii2022.EMC

/-- Proposition 4 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 4): if `F ⊂ \binom{[m]}{k}` is initial
and `ν(F) ≤ s`, then `(s + 1, 2(s + 1), …, k(s + 1)) ∉ F`; consequently, for every `F ∈ F` there
is some `i`, `1 ≤ i ≤ k`, with `|F ∩ [i(s + 1) − 1]| ≥ i` (10).

**Formalization Note.** The set `(s+1, 2(s+1), …, k(s+1))` is the image of `j ↦ j(s+1)` on
`Finset.Icc 1 k`; `[i(s+1) − 1] = Finset.Icc 1 (i * (s + 1) - 1)` (exact for `i ≥ 1`). The
Sect. 1 standing assumption "positive integers k, s" is kept as `1 ≤ k`, `1 ≤ s`; at `k = 0` the
first claim fails for `F = {∅}`. -/
theorem initial_dense_prefix (m k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Finset.Icc 1 m).powersetCard k) (hinit : IsInitial m k F)
    (hν : matchingNumber F ≤ s) :
    (Finset.Icc 1 k).image (fun j => j * (s + 1)) ∉ F ∧
      ∀ A ∈ F, ∃ i, 1 ≤ i ∧ i ≤ k ∧ i ≤ (A ∩ Finset.Icc 1 (i * (s + 1) - 1)).card := by sorry

end FranklKupavskii2022.EMC
