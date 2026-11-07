-- Prove2me | Theorems.Thm_MinBisectFPT_theorem_1_1
-- name    : MinBisectFPT.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:10.003295+00:00
-- url     : https://prove2.me/theorems/a5aa6218-3746-47be-90cd-f4eeb4c425f1
-- title:
--   Theorem 1.1 — all $C_G(\ell,j)$, $j\le k$, in time $2^{O(k)}n^{O(1)}$
-- statement:
--   There is an algorithm that, given a graph $G$ with $n$ vertices and an integer $k\ge0$, computes in time $2^{O(k)}n^{O(1)}$, for all $0\le\ell\le n$ and $0\le j\le k$, the number
--   $$C_G(\ell,j)=\bigl|\{X\subseteq V(G):|X|=\ell\text{ and }|\delta(X)|=j\}\bigr|.$$
--
--   $G$ is arbitrary: it may be disconnected or edgeless, and $n=0$ is allowed. There is no relation between $k$ and $n$. Every entry of the table is exact. Minimum Bisection in time $2^{O(k)}n^{O(1)}$ follows, improving on $2^{O(k\log k)}n^{O(1)}$.
--
--   Differences from the source:
--   - reading: "an algorithm … in time $2^{O(k)}n^{O(1)}$" → one bundled `TM2` machine `M` and one constant `c`, chosen before the instance, within `c * 2^(c*k) * (n+1)^c` steps; reason: the paper counts bit operations (p.15) and fixes no machine; a RAM of this cost runs on a `TM2` with polynomial overhead, and the bound is closed under polynomials; `n+1` because a machine still runs at `n = 0, 1`
--   - encoding: $G$ with $n$ vertices; the numbers → `SimpleGraph (Fin n)` with its adjacency bits; the table in row-major order; reason: same data; the bound is in $n$ and $k$, never in the input length
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MinBisectFPT_encodeCounts

open scoped Classical

namespace MinBisectFPT

/-- **Theorem 1.1.** Anand, Kipouridis, Węgrzycki, *Counting over Unbreakable Decompositions*, STOC 2027
submission (manuscript sha256 8db80a52…), Theorem 1.1, p.2: "There is an algorithm that, given a graph
G with n vertices and an integer k ≥ 0, computes in time 2^{O(k)} n^{O(1)}, for all 0 ≤ ℓ ≤ n and
0 ≤ j ≤ k, the number C_G(ℓ, j) = |{X ⊆ V(G) : |X| = ℓ and |δ(X)| = j}|."

**Formalization Note** One bundled Turing machine `M` (Mathlib's `TM2`, deterministic, bit cost; the
paper counts bit operations, p.15, and fixes no machine) and one constant `c`, chosen before the
instance. `(n + 1)^c` in place of `n^{O(1)}`, since a machine still runs at `n = 0, 1`. No hypothesis on
`G` (disconnected and edgeless graphs and `n = 0` are in) and no relation between `k` and `n`. -/
theorem theorem_1_1 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ),
      HMBinPacking.OutputsWithin M (encodeInput G k) (encodeCounts G k)
        (c * 2 ^ (c * k) * (n + 1) ^ c) := by sorry

end MinBisectFPT
