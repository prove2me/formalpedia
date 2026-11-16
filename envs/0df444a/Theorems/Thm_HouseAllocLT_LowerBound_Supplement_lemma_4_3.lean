-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_lemma_4_3
-- name    : HouseAllocLT.LowerBound.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:16:32.385034+00:00
-- url     : https://prove2.me/theorems/a9beda01-9e24-4513-8845-56294d350fa2
-- title:
--   Lemma 4.3 — moving an agent earlier cannot worsen its rank
-- statement:
--   Let $n,m\ge1$, fix a routine, a profile $P$ and an agent $i$. Let $\pi,\pi'$ be orders that agree on the relative order of all agents other than $i$ and place $i$ strictly earlier in $\pi'$ than in $\pi$. Then
--   $$\mathrm{rank}_i\big(M_{\pi'}(P)(i)\big)\le \mathrm{rank}_i\big(M_{\pi}(P)(i)\big),$$
--   where an unmatched agent has rank $+\infty$.
--
--   This monotonicity is used in Lemma 4.7 to show that late starting agents stay unmatched.
--
--   Differences from the source:
--   - encoding: ranks and classes numbered from one → classes numbered from zero (paper rank j is class j−1); reason: a bijection of indices, no instance changes
--   - encoding: a fixed deterministic maximum-matching routine → a universally quantified routine `MM`; reason: the source states the result for whatever fixed routine RPG uses, which is the same claim
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 4.3, PDF p. 11 (printed p. 9); proof PDF p. 16 (printed p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_RPG

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Lemma 4.3, PDF p. 11 (printed p. 9). Fix an agent `i` and the relative order of all other
agents. Moving `i` earlier in RPG cannot worsen its assigned rank (unmatched = rank `⊤`). -/
theorem lemma_4_3 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (MM : MaxMatchingRoutine n m)
    (P : Profile n m) (i : Fin n) (π π' : Equiv.Perm (Fin n))
    (hrel : ∀ j k : Fin n, j ≠ i → k ≠ i → (π j < π k ↔ π' j < π' k))
    (hearlier : π' i < π i) :
    agentRank P (rpgOut MM P π') i ≤ agentRank P (rpgOut MM P π) i := by sorry

end HouseAllocLT.LowerBound.Supplement
