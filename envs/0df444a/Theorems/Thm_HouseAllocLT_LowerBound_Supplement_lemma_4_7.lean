-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_lemma_4_7
-- name    : HouseAllocLT.LowerBound.Supplement.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:19:08.2188+00:00
-- url     : https://prove2.me/theorems/5240bc08-d585-4ee6-97c2-da28cf3f94c1
-- title:
--   Lemma 4.7 — the recipient-chain injection
-- statement:
--   Let $n,m\ge1$ and fix a routine. Suppose a rank-maximal benchmark $M^*$ matches every agent and every list ends at its benchmark class. Let $u\in(0,1)^N$ have pairwise distinct entries (smaller keys first) and let $t\in(0,1)$ differ from every $u_i$. For every matching $M$ with the best class vector for the order of $u$ there is an injection
--   $$F_t(u)\longrightarrow\{q: q\text{ is matched in }M,\ u_q<t\},$$
--   where $F_t(u)=\{i: i\text{ is unmatched in }M(u^{i,t})\}$ is defined by the comparison runs.
--
--   Taking expectations of the resulting cardinality inequality gives the integral inequality behind Lemma 4.8.
--
--   Differences from the source:
--   - encoding: ranks and classes numbered from one → classes numbered from zero (paper rank j is class j−1); reason: a bijection of indices, no instance changes
--   - encoding: a fixed deterministic maximum-matching routine → a universally quantified routine `MM`; reason: the source states the result for whatever fixed routine RPG uses, which is the same claim
--   - encoding: an injection from F_t(u) into the matched early agents → a function on all agents mapping F_t(u) into that set and injective on F_t(u); reason: restriction to F_t(u) gives the injection and conversely any injection extends
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 4.7, PDF p. 12 (printed p. 10), with the setting of §4.4 and (11); proof PDF pp. 17–18 (printed pp. 15–16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_RPG

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Lemma 4.7, PDF p. 12 (printed p. 10). Suppose a rank-maximal benchmark `M*` matches every
agent (agent `i` in its class `R_i`) and every list ends at its benchmark class. For pairwise
distinct keys `u` in `(0, 1)`, every `t ∈ (0, 1)` different from all keys, and every matching `M`
with the best class vector for the key order of `u`, there is an injection
`F_t(u) → {q : q is matched in M, u_q < t}`. -/
theorem lemma_4_7 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (MM : MaxMatchingRoutine n m)
    (P : Profile n m) (Mstar : Assignment n m) (hRM : RankMaximal P Mstar)
    (R : Fin n → ℕ) (hR : ∀ i, ∃ a ∈ (P i).classes (R i), (i, a) ∈ Mstar)
    (hend : ∀ i, (P i).length = R i + 1)
    (u : Fin n → ℝ) (hu : Function.Injective u) (hu01 : ∀ i, u i ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (htu : ∀ i, u i ≠ t)
    (M : Assignment n m) (hM : IsLexBest P (keyPos u) M) :
    ∃ f : Fin n → Fin n,
      (∀ i ∈ startingAgents MM P u t, Matched M (f i) ∧ u (f i) < t) ∧
      Set.InjOn f (startingAgents MM P u t : Set (Fin n)) := by sorry

end HouseAllocLT.LowerBound.Supplement
