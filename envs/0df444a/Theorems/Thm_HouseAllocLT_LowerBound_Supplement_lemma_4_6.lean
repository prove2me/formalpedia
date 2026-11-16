-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_lemma_4_6
-- name    : HouseAllocLT.LowerBound.Supplement.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:18:16.196511+00:00
-- url     : https://prove2.me/theorems/4b32c3e2-41c8-444c-bb38-fa6fb3748c10
-- title:
--   Lemma 4.6 — truncating at benchmark classes keeps the benchmark and cannot grow RPG
-- statement:
--   Let $n,m\ge1$ and fix a routine. Suppose $P$ has a rank-maximal matching $M^*$ that matches every agent; put $a_i=M^*(i)$ and $R_i=\mathrm{rank}_i(a_i)$. Let $Q$ keep the whole classes $C_1^i,\ldots,C_{R_i}^i$ of each agent $i$. Then $M^*$ is rank maximal at $Q$, and
--   $$|M_\pi(P)|\ge|M_\pi(Q)|\quad\text{for every order }\pi.$$
--
--   This is the second reduction step in the proof of Lemma 4.10.
--
--   Differences from the source:
--   - encoding: ranks and classes numbered from one → classes numbered from zero (paper rank j is class j−1); reason: a bijection of indices, no instance changes
--   - encoding: a fixed deterministic maximum-matching routine → a universally quantified routine `MM`; reason: the source states the result for whatever fixed routine RPG uses, which is the same claim
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 4.6, PDF p. 12 (printed p. 10); proof PDF p. 17 (printed p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_RPG

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Lemma 4.6, PDF p. 12 (printed p. 10). Suppose `M*` is rank maximal at `P` and matches every
agent, with `a_i = M*(i)` in class `R_i` (0-based). Let `Q` keep the whole classes
`C_1^i, …, C_{R_i}^i` (0-based `0, …, R_i`). Then `M*` remains rank maximal at `Q`, and
`|M_π(P)| ≥ |M_π(Q)|` for every order `π`. -/
theorem lemma_4_6 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (MM : MaxMatchingRoutine n m)
    (P : Profile n m) (Mstar : Assignment n m) (hRM : RankMaximal P Mstar)
    (R : Fin n → ℕ) (hR : ∀ i, ∃ a ∈ (P i).classes (R i), (i, a) ∈ Mstar) :
    RankMaximal (fun i => truncate (P i) (R i + 1)) Mstar ∧
    ∀ π : Equiv.Perm (Fin n),
      (rpgOut MM (fun i => truncate (P i) (R i + 1)) π).card ≤ (rpgOut MM P π).card := by sorry

end HouseAllocLT.LowerBound.Supplement
