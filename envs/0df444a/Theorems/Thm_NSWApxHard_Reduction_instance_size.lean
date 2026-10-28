-- Prove2me | Theorems.Thm_NSWApxHard_Reduction_instance_size
-- name    : NSWApxHard.Reduction.instance_size
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:34.662036+00:00
-- url     : https://prove2.me/theorems/bfae77d4-e1fd-4d10-b858-1d3a3f51ce38
-- title:
--   §2, p. 2 — the reduced instance has n = N + M = 2.5N agents and m = c_min N + M + 3N items
-- statement:
--   Let $G$ be a 3-regular graph on $N$ vertices, so that it has $M=1.5N$ edges, and build the reduced instance with $k$ vertex items. Then the numbers $n$ of agents and $m$ of items satisfy
--   $$n = N+M = 2.5N,\qquad m = k + M + 3N = k + 4.5N .$$
--   With $k=c_{\min}N$ this is the paper's $m=(4.5+c_{\min})N$.
--
--   The count fixes the exponent $1/n = 1/(2.5N)$ in every welfare computation of the reduction and shows the instance has polynomial size.
--
--   **Formalization Note** The identities are stated doubled, $2n=5N$ and $2m=2k+9N$, in the natural numbers.
--
--   Differences from the source:
--   - generalization: c_min N vertex items → any number k of vertex items; reason: the count holds for every k, and k = c_min N gives the page's identity.
--   - encoding: n = 2.5N, m = (4.5 + c_min)N → 2n = 5N, 2m = 2k + 9N in ℕ; reason: same identities without fractions.
--   - encoding: a 3-regular graph with N vertices → a graph on Fin N, N = 0 allowed; reason: for N = 0 both sides are 0, so no instance of the page changes.
-- source:
--   Lee, APX-Hardness of Maximizing Nash Social Welfare with Indivisible Items, arXiv:1507.01159v1, p. 2, §2 (sentence after the reduction)

import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Lee, p. 2: for a 3-regular graph on `N` vertices with `k` vertex items, the reduced instance
has `n = N + M = 2.5N` agents and `m = k + M + 3N = k + 4.5N` items. -/
theorem instance_size {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ)
    (hG : IsCubic G) :
    2 * Fintype.card (Agent G) = 5 * N ∧ 2 * Fintype.card (Item G k) = 2 * k + 9 * N := by sorry

end NSWApxHard.Reduction
