-- Prove2me | Theorems.Thm_LipStableCA_observation_5_10
-- name    : LipStableCA.observation_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:43.451198+00:00
-- url     : https://prove2.me/theorems/785c2201-01db-43f8-8c4d-38b9916ffec7
-- title:
--   Observation 5.10 — the welfare of Mechanism 3 is at least half the sum of block maxima
-- statement:
--   For a realization of the random choices of Mechanism 3 and $b\in[k]$, let $V_b$ be the largest value $v_i(M_b)$ of a bidder $i$ with $Y_i=M_b$, with $V_b=0$ if $M_b=\emptyset$ or there is no such bidder. For every realization of the random choices, the welfare of the allocation at $v$ is at least
--   $$\frac12\sum_{b\in[k]}V_b.$$
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: every realization of the random choices → every seed with weights in the support $[-1,1]^n$; reason: the mechanism draws $Z\in[-1,1]^n$ (Mechanism 1, line 3)
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Observation 5.10, p.27

import Definitions.Def_LipStableCA_randomBlock
open ComplementFreeCA.CFRounding

namespace LipStableCA

/-- **Observation 5.10.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.27. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. every seed with weights in the support `[-1,1]^n`: the mechanism draws `Z∈[-1,1]^n` (Mechanism 1, line 3). -/
theorem observation_5_10 {n m : ℕ} (hm : 1 ≤ m) (ord : LinearOrder (Finset (Fin n))) (v : Profile n m)
    (hv : IsProfile v) (ω : BlockSeed n m) (hω : ∀ i, ω.2.2 i ∈ Set.Icc (-1 : ℝ) 1) :
    1 / 2 * ∑ b ∈ Finset.range (blockCount ω), blockValue v ω b ≤
      welfare v ((randomBlock ord : Mechanism n m (BlockSeed n m)).alloc v ω).1 := by sorry

end LipStableCA
