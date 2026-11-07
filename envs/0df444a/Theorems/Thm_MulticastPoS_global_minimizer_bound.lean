-- Prove2me | Theorems.Thm_MulticastPoS_global_minimizer_bound
-- name    : MulticastPoS.global_minimizer_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:34.416823+00:00
-- url     : https://prove2.me/theorems/80468b4d-4dca-4aac-9f33-66a7732ec298
-- title:
--   Proof of Theorem 1.1 — every global potential minimizer has $SC\le 10(1+\lfloor\log_2\log_2 n\rfloor)\,OPT$
-- statement:
--   Let the edge costs be nonnegative and let $n$ be the number of players. Every global minimizer $P$ of the potential satisfies
--
--   $$
--   SC(P)\le 10\bigl(1+\lfloor\log_2\log_2 n\rfloor\bigr)\,SC(Q)\quad\text{for every path profile } Q,
--   $$
--
--   hence $SC(P)\le 10(1+\lfloor\log_2\log_2 n\rfloor)\,OPT=O(\log\log n)\,OPT$. The proof divides the positive loads into the intervals $[\tau_r,\tau_{r+1})$ with $\tau_0=1$, $\tau_1=4$, $\tau_{r+1}=\tau_r^2$; each costs at most $10\,OPT$, and only those with $r\le\lfloor\log_2\log_2 n\rfloor$ can contain an edge.
--
--   With Corollary 2.1, which makes a global minimizer a Nash equilibrium, this gives the main theorem.
--
--   **Formalization Note** $\lfloor\log_2\log_2 n\rfloor$ is `Nat.log 2 (Nat.log 2 n)`, which is $0$ for $n\le 3$ (one interval $[1,4)$).
--
--   Differences from the source:
--   - encoding: finite undirected graph G = (V, E); player i chooses a simple path P_i from s_i to t; n players → SimpleGraph on a Fintype V; strategies are the edge sets p.edges.toFinset of walks p : G.Walk (s i) t with p.IsPath; players a Fintype ι; reason: the same games: loops never lie on a simple path, a parallel edge is equivalent to a subdivided edge with costs c_e and 0 (same strategies, payments, potential and social cost), and payments, loads, Φ and SC depend on a path only through its edge set
--   - encoding: a nonnegative cost c_e on each edge e → c : Sym2 V → ℝ with 0 ≤ c e for every e ∈ G.edgeSet; reason: the values of c off the graph never enter: no strategy contains a non-edge
--   - encoding: standing assumption: a path from each source to t exists (p.1) → not a separate hypothesis; reason: it is implied by the hypothesis that a (global-minimizer) profile exists, since every player then has an s_i–t path
--   - encoding: OPT = c(T⋆), the cost of a fixed minimum-cost tree connecting all sources to t → the bound holds against SC(Q) for every path profile Q; reason: there are finitely many profiles and, by the optimum-as-tree milestone, the least SC(Q) equals OPT, so 'for every Q' is equivalent
--   - generalization: SC(P) = O(log log n) OPT → SC(P) ≤ 10 (1 + Nat.log 2 (Nat.log 2 n)) SC(Q); reason: the explicit bound is what the proof gives (each interval costs at most 10 OPT; the intervals meeting [1, n] are r = 0, …, ⌊log₂ log₂ n⌋) and implies the O-bound
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), proof of Theorem 1.1 and the paragraph after it, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MulticastPoS_game
import Definitions.Def_MulticastPoS_socialCost
import Definitions.Def_MulticastPoS_IsGlobalMin

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace MulticastPoS

/-- Proof of Theorem 1.1 and the remark after it (Huang–Yuan, *An O(log log n) Upper Bound on the
Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript
(sha256 dd0e08d0…f6d4), p.6): the positive loads are divided into the intervals
`[τ_r, τ_{r+1})` with `τ₀ = 1`, `τ₁ = 4`, `τ_{r+1} = τ_r²`, each of which costs at most
`10 OPT`; since every load is at most `n`, the intervals that can contain an edge are those with
`r ≤ ⌊log₂ log₂ n⌋`, and adding their costs bounds `SC(P)`. The same bound holds for every global
potential minimizer: with nonnegative edge costs, every global minimizer `P` satisfies
`SC(P) ≤ 10 (1 + ⌊log₂ log₂ n⌋) SC(Q)` for every profile `Q`.

**Formalization Note** `n = Fintype.card ι`; `⌊log₂ log₂ n⌋` is `Nat.log 2 (Nat.log 2 n)`, which
is `0` for `n ≤ 3` (one interval `[1, 4)`). `OPT` is replaced by the social cost of an arbitrary
profile `Q` (the minimum over profiles equals `OPT`). The paper prints `O(log log n)`; the
explicit constant is the one its proof gives. -/
theorem global_minimizer_bound {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    [DecidableEq ι] (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s : ι → V)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (P : ι → Finset (Sym2 V))
    (hP : IsGlobalMin (game G c t s) P) (Q : ι → Finset (Sym2 V))
    (hQ : IsProfile (game G c t s) Q) :
    socialCost c P ≤
      10 * ((1 + Nat.log 2 (Nat.log 2 (Fintype.card ι)) : ℕ) : ℝ) * socialCost c Q := by sorry

end MulticastPoS
