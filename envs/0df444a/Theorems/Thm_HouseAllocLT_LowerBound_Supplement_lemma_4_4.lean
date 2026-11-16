-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_lemma_4_4
-- name    : HouseAllocLT.LowerBound.Supplement.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:17:01.237336+00:00
-- url     : https://prove2.me/theorems/9e87c55c-03ec-4b82-956b-696397c9416a
-- title:
--   Lemma 4.4 — appending classes cannot shrink the RPG output
-- statement:
--   Let $n,m\ge1$, fix a routine, an order $\pi$ and a profile $P$ (ties allowed). Let $P'$ agree with $P$ except that agent $i$'s list is extended by new classes after its last class, every existing class unchanged. Then
--   $$|M_\pi(P)|\le|M_\pi(P')|,$$
--   and if $i$ is matched in $M_\pi(P)$, then $M_\pi(P')$ and $M_\pi(P)$ have the same class-vector entry at every old class entry $(i',j)$, $j\le r_{i'}$.
--
--   It gives the size comparison of Lemma 4.6 one agent at a time.
--
--   Differences from the source:
--   - encoding: ranks and classes numbered from one → classes numbered from zero (paper rank j is class j−1); reason: a bijection of indices, no instance changes
--   - encoding: a fixed deterministic maximum-matching routine → a universally quantified routine `MM`; reason: the source states the result for whatever fixed routine RPG uses, which is the same claim
--   - encoding: "the optimal vector of all old class entries" → the entries of the RPG outputs $M_\pi(P')$ and $M_\pi(P)$ at every old class entry; reason: the RPG output is an optimum and all optima share one class vector (Lemma 4.1, PDF p. 11)
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 4.4, PDF p. 12 (printed p. 10); proof PDF pp. 16–17 (printed pp. 14–15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_RPG

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Lemma 4.4, PDF p. 12 (printed p. 10). Fix a profile `P` and an order `π`, ties allowed.
`P'` adds new classes at the end of agent `i`'s list without changing any existing class. Then
the output size cannot decrease, and if `i` was already matched, the entries of the class vector
at all old class entries are unchanged. -/
theorem lemma_4_4 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (MM : MaxMatchingRoutine n m)
    (P P' : Profile n m) (i : Fin n)
    (hother : ∀ j : Fin n, j ≠ i → P' j = P j)
    (hlen : (P i).length ≤ (P' i).length)
    (hkeep : ∀ j < (P i).length, (P' i).classes j = (P i).classes j)
    (π : Equiv.Perm (Fin n)) :
    (rpgOut MM P π).card ≤ (rpgOut MM P' π).card ∧
    (Matched (rpgOut MM P π) i →
      ∀ (i' : Fin n) (j : ℕ), j < (P i').length →
        entryVal P' (rpgOut MM P' π) i' j = entryVal P (rpgOut MM P π) i' j) := by sorry

end HouseAllocLT.LowerBound.Supplement
