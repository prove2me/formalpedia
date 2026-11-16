-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_Supplement_lemma_4_5
-- name    : HouseAllocLT.LowerBound.Supplement.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:17:25.709789+00:00
-- url     : https://prove2.me/theorems/44d8650d-2007-48b9-bd9c-89bf825ede87
-- title:
--   Lemma 4.5 — reduction to an instance whose benchmark matches everyone
-- statement:
--   Let $n,m\ge1$, fix a routine, a profile $P$ and a rank threshold $h$ with $r=R_h^*(P)>0$. End every list after rank $h$. Then one can delete agents only, keeping exactly $r$ agents (an injection $\sigma$ of $\{1,\ldots,r\}$ into the agents) and all $m$ objects, so that the resulting instance $Q$ has a rank-maximal matching that matches all $r$ agents, and
--   $$\mathbb E\,|\mathrm{RPG}(Q)|\le X_h^{\mathrm{RPG}}(P),$$
--   the left side using the uniform order on the $r$ remaining agents and any fixed routine.
--
--   This is the first reduction step in the proof of Lemma 4.10.
--
--   Differences from the source:
--   - encoding: ranks and classes numbered from one → classes numbered from zero (paper rank j is class j−1); reason: a bijection of indices, no instance changes
--   - encoding: a fixed deterministic maximum-matching routine → a universally quantified routine `MM`; reason: the source states the result for whatever fixed routine RPG uses, which is the same claim
--   - reading: the routine used on the r-agent instance (unspecified) → every routine on that instance; reason: the source fixes no routine for the smaller instance; the strongest reading is stated, which the proof (sizes depend only on the optimal class vector) supports
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 4.5, PDF p. 12 (printed p. 10); proof PDF p. 17 (printed p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_RPG

open scoped BigOperators ENNReal
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

/-- Lemma 4.5, PDF p. 12 (printed p. 10). Put `r = R*_h(P) > 0` and end every list after rank
`h`. Deleting only agents (an injection `σ` of the `r` kept agents), one obtains an instance with
exactly `r` agents and all `m` objects in which a rank-maximal matching matches every agent, and
whose expected RPG size (uniform order on its own agents, any fixed routine) is at most
`X_h^{RPG}(P)`. -/
theorem lemma_4_5 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (MM : MaxMatchingRoutine n m)
    (P : Profile n m) (h : ℕ) (hr : 0 < benchmarkPrefix P h) :
    ∃ σ : Fin (benchmarkPrefix P h) ↪ Fin n,
      (∃ M : Assignment (benchmarkPrefix P h) m,
        RankMaximal (fun j => truncate (P (σ j)) h) M ∧ ∀ j, Matched M j) ∧
      ∀ MM' : MaxMatchingRoutine (benchmarkPrefix P h) m,
        expectedSize (rpg MM') (fun j => truncate (P (σ j)) h) ≤ expectedPrefix (rpg MM) P h := by sorry

end HouseAllocLT.LowerBound.Supplement
