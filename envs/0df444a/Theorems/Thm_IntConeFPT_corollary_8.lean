-- Prove2me | Theorems.Thm_IntConeFPT_corollary_8
-- name    : IntConeFPT.corollary_8
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T00:39:17.075335+00:00
-- url     : https://prove2.me/theorems/eebaeed3-484a-4bfa-8149-082f82d7208e
-- title:
--   Corollary 8 (Candidate Support Bound) — at most $2^{\tau(d+1+d^2 2^d)}$ candidate residue tuples
-- statement:
--   Let $d\ge1$ and $\tau\ge0$. The number of tuples $R=(R^{(1)},\dots,R^{(\tau)})$ with $R^{(t)}\subseteq\{0,\dots,2^d-1\}^d$ and $|R^{(t)}|\le2^d$ for every $t$ is at most
--   $$
--   2^{\tau\,(d+1+d^2 2^d)}.
--   $$
--   This is the explicit bound derived in the proof (p.11); it implies the printed bound $2^{\tau2^{O(d)}}$, since $d+1+d^22^d\le2^{4d}$ for $d\ge1$.
--
--   The algorithm enumerates these tuples, so this count enters the running time of Proposition 14.
--
--   **Formalization Note** Residue vectors are `Fin d → Fin (2^d)`; the tuples are counted as a `Finset.filter` of all functions `Fin τ → Finset (Fin d → Fin (2^d))`.
--
--   Differences from the source:
--   - generalization: at most 2^{τ2^{O(d)}} candidate tuples → at most 2^(τ * (d + 1 + d^2 * 2^d)) (the explicit bound of the proof, p.11); reason: the explicit bound implies the printed one because d + 1 + d²2^d ≤ 2^{4d} for d ≥ 1
--   - encoding: R^(t) ⊆ {0, …, 2^d − 1}^d → R : Fin τ → Finset (Fin d → Fin (2^d)); reason: Lean convention; same sets
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Corollary 8, p.11

import Mathlib

namespace IntConeFPT

/-- **Corollary 8 (Candidate Support Bound).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Corollary 8, p.11: "The number of candidate active residue
tuples R = (R^(1), …, R^(τ)) with R^(t) ⊆ {0, …, 2^d − 1}^d and |R^(t)| ≤ 2^d is at most
2^{τ2^{O(d)}}."

Stated with the explicit bound of the proof (p.11): at most `2^{τ (d + 1 + d² 2^d)}` tuples.

**Formalization Note.** A residue vector is `Fin d → Fin (2^d)`; `d ≥ 1` is the paper's standing
assumption. The explicit bound implies the printed `2^{τ 2^{O(d)}}` (since
`d + 1 + d² 2^d ≤ 2^{4d}` for `d ≥ 1`). -/
theorem corollary_8 (d τ : ℕ) (hd : 1 ≤ d) :
    ((Finset.univ : Finset (Fin τ → Finset (Fin d → Fin (2 ^ d)))).filter
      (fun R => ∀ t, (R t).card ≤ 2 ^ d)).card ≤ 2 ^ (τ * (d + 1 + d ^ 2 * 2 ^ d)) := by sorry

end IntConeFPT
