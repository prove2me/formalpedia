-- Prove2me | Theorems.Thm_FourWayStream_ARHM_good_schedules
-- name    : FourWayStream.ARHM.good_schedules
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:44:20.583205+00:00
-- url     : https://prove2.me/theorems/49772844-0f13-4591-b59a-fe70344649f9
-- title:
--   Lemma 5.6 — good schedules: a schedule is bad with probability $<3/100$
-- statement:
--   **Lemma 5.6 (Good schedules).** Let $N$ be even, $2\le m\le\lfloor\sqrt N\rfloor$, $\mu=100m$, $L=\mu^2$ and $P=\lceil9\log_2(m+1)\rceil$. Call a schedule good if no request arrives in the initial interval (gaps $0,\dots,\mu N-1$) and no bank must serve more than $P$ requests. In a uniformly random order,
--   $$P[\text{the schedule is not good}]<\frac{3}{100}.$$
--
--   Together with Lemma 5.4 this gives the correctness of the random-order quantum algorithm (Proposition 5.7).
--
--   Differences from the source:
--   - encoding: bank β serves gaps βµN, …, (β+1)µN − 1 for 1 ≤ β < µ, bank µ serves gap NL, gaps 0, …, µN − 1 are the initial interval → the bank of gap g is ⌊g/(µN)⌋ (0 = initial interval); reason: the three cases of p.21 are exactly ⌊g/(µN)⌋ for 0 ≤ g ≤ NL = µ²N
--   - encoding: random order: a uniformly random permutation of the NL + m labeled items → the average over all bijections Fin (N·L + m) ≃ (Fin N × Fin L) ⊕ Fin m (positions to labeled occurrences); reason: the uniform distribution on these bijections is the uniform random permutation of the labeled occurrences
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5.1.1, pp.21–22, Lemma 5.6 (good schedule defined p.21, P p.20)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Rebuild

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Lemma 5.6 (Good schedules), p.22. Let `N` be even, `2 ≤ m ≤ ⌊√N⌋`, `µ = 100m`, `L = µ²`,
`P = ⌈9 log(m+1)⌉`. Under the uniformly random arrival order, the schedule is not good (a request
arrives in the initial interval, or some bank must serve more than `P` requests) with probability
less than `3/100`. -/
theorem good_schedules (N m : ℕ) (hN : Even N) (hm : 2 ≤ m) (hmN : m ≤ Nat.sqrt N) :
    ((Finset.univ.filter (fun σ : Arrival N m ((100 * m) ^ 2) =>
        ¬ IsGoodSchedule (100 * m) (bankSize m) σ)).card : ℝ) /
      (Fintype.card (Arrival N m ((100 * m) ^ 2)) : ℝ) < 3 / 100 := by sorry

end FourWayStream.ARHM
