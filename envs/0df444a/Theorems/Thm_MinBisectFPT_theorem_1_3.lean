-- Prove2me | Theorems.Thm_MinBisectFPT_theorem_1_3
-- name    : MinBisectFPT.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:08.355183+00:00
-- url     : https://prove2.me/theorems/630ea02f-5e58-478f-9756-b7111e4b8286
-- title:
--   Theorem 1.3 — unbreakable decomposition in time $2^{O(k)}n^{O(1)}$
-- statement:
--   There is an algorithm that, given a connected graph $G$ with $n$ vertices and an integer $k\ge1$, computes in time $2^{O(k)}n^{O(1)}$ a rooted tree decomposition of $G$ with at most $n$ nodes and the following properties.
--
--   1. (D1) Every adhesion has at most $2k$ vertices.
--   2. (D2) For every non-root node $t$, the component $\alpha(t)$ is nonempty, $G[\alpha(t)]$ is connected, and $N_G(\alpha(t))=\sigma(t)$.
--   3. (D3) Every bag $\beta(t)$ is $(3k,k)$-edge-unbreakable in the subtree graph $G_t$.
--
--   This is the first construction in single-exponential time with adhesions of size $O(k)$ and $(O(k),k)$-edge-unbreakable bags, and the dynamic program of the mission runs on it.
--
--   Differences from the source:
--   - reading: "an algorithm … in time $2^{O(k)}n^{O(1)}$" → one bundled `TM2` machine `M` and one constant `c`, chosen before the instance, within `c * 2^(c*k) * (n+1)^c` steps; reason: the paper counts bit operations (p.15) and fixes no machine; a RAM of this cost runs on a `TM2` with polynomial overhead, and the bound is closed under polynomials; `n+1` because a machine still runs at `n = 0, 1`
--   - encoding: $G$ on $n$ vertices → `SimpleGraph (Fin n)`, encoded by its adjacency bits; the output word is pinned by `encodeTD`; reason: same data
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Theorem 1.3, p.3; restated p.16

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MinBisectFPT_encodeTD
import Definitions.Def_MinBisectFPT_IsUnbreakableTD

open scoped Classical

namespace MinBisectFPT

/-- **Theorem 1.3.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Theorem 1.3, p.3, restated p.16: "There is an algorithm that, given a connected
graph G with n vertices and an integer k ≥ 1, computes in time 2^{O(k)} n^{O(1)} a rooted tree
decomposition of G with at most n nodes" and properties (D1)–(D3).

**Formalization Note** One bundled Turing machine `M` and one constant `c` before the instance, as in
Theorem 1.1. The word `encodeTD T` pins the output. -/
theorem theorem_1_3 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.Connected → ∀ k : ℕ, 1 ≤ k → ∃ T : RootedTD n,
        IsRootedTD G T ∧ T.N ≤ n ∧ IsUnbreakableTD G T k ∧
          HMBinPacking.OutputsWithin M (encodeInput G k) (encodeTD T)
            (c * 2 ^ (c * k) * (n + 1) ^ c) := by sorry

end MinBisectFPT
