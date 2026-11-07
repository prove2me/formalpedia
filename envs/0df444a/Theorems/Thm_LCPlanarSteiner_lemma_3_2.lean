-- Prove2me | Theorems.Thm_LCPlanarSteiner_lemma_3_2
-- name    : LCPlanarSteiner.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:02.329394+00:00
-- url     : https://prove2.me/theorems/cd0e1d11-9a0b-4f45-a37c-291d5ba2f072
-- title:
--   Lemma 3.2 — cost-bounded arrivals: $A(v) \le a(b) + \ell(Q)$ for $c(Q) \le \Gamma$, extensions of cost $\le 2\Gamma$
-- statement:
--   Let $G$ be a graph with nonnegative costs and lengths, $r$ a root, $E_R$ a set of owned arcs, $B$ a set of boundary vertices, $F$ the purchased arcs, and $a(b) = \mathrm{dist}_F(r, b)$ the actual labels. Let $\Gamma \ge 0$.
--
--   **Lemma 3.2 (Cost-bounded arrivals).** In polynomial binary time one can compute, for every vertex $v$, a possibly infinite arrival $A(v)$ and, when $A(v)$ is finite, an owned extension $Q_v$, such that
--   1. $A(v) \le a(b) + \ell(Q)$ whenever $b \in B$ and $Q$ is a walk of owned arcs from $b$ to $v$ with $c(Q) \le \Gamma$ (in particular $A(v)$ is then finite);
--   2. every returned extension $Q_v$ is a simple path of owned arcs from some $b \in B$ with $c(Q_v) \le 2\Gamma$, and it arrives by $A(v)$: $a(b) + \ell(Q_v) \le A(v)$, through an actually paid prefix.
--
--   For $\Gamma = 0$ the extensions have zero cost.
--
--   Arrivals measure how early each vertex can be reached by buying a cheap owned extension after the already purchased union; they drive the forward profiles of Lemma 3.3.
--
--   **Formalization Note** "$A(v) \le a(b) + \ell(Q)$" is stated for every walk $W$ from $r$ to $b$ inside $F$, so boundary vertices with infinite label impose nothing.
--
--   Differences from the source:
--   - generalization: Q : b ⇝ v an owned path with c(Q) ≤ Γ → every owned walk from b to v whose summed cost is ≤ Γ; reason: walks contain paths, and the rounding argument (rounded cost at most n) applies to walks
--   - generalization: a region (C, B, E_R) of the recursion → arbitrary arc set E_R and vertex set B; reason: the proof uses no region property, so the region case is a special case
--   - generalization: original owned extensions Q_v → simple paths; reason: the proof erases cycles
--   - reading: polynomial binary time and O(n²) states suffice → one function computed by a Turing machine in polynomial time on a fixed binary encoding; the state count is not stated; reason: the paper names no machine model, and the number of DP states describes the construction, not its output
--   - encoding: the cases Γ > 0 and Γ = 0 → one statement for Γ ≥ 0 with c(Q_v) ≤ 2Γ; possibly infinite A(v) → a finiteness flag with a rational value; reason: 2Γ = 0 is the zero-cost case; Lean convention
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.2, p.5; labels and query graph, §3.1, p.5

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsSPath
import Definitions.Def_LCPlanarSteiner_plen
import Definitions.Def_LCPlanarSteiner_encArrIn
import Definitions.Def_LCPlanarSteiner_encArrOut

namespace LCPlanarSteiner

/-- **Lemma 3.2 (Cost-bounded arrivals).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.2, p.5: "For Γ > 0, polynomial binary time and O(n²) states suffice to compute
possibly infinite arrivals A(v) and original owned extensions Q_v for finite values, such that
A(v) ≤ a(b) + ℓ(Q) whenever Q : b ⇝ v, c(Q) ≤ Γ. Each returned extension costs at most 2Γ and
arrives by A(v). For Γ = 0, the same assertion holds with zero extension cost." Labels (§3.1, p.5):
"a(b) = dist_F(r, b); omit infinite labels".

There is a function `alg`, computable by a Turing machine in time polynomial in the binary input,
mapping a query `(G, E_R, B, F, r, Γ)` to one entry `(finite, A(v), Q_v)` per vertex `v < n`, such
that for every well-formed graph, root `r < n` and budget `Γ ≥ 0`, and every vertex `v`:
1. (comparison) for every boundary vertex `b ∈ B`, every walk `Q` from `b` to `v` of owned arcs
   (in `E_R`) with `c(Q) ≤ Γ`, and every walk `W` from `r` to `b` in `F`, the arrival `A(v)` is
   finite and `A(v) ≤ ℓ(W) + ℓ(Q)`; that is, `A(v) ≤ a(b) + ℓ(Q)`;
2. (extension) if `A(v)` is finite, `Q_v` is a simple path of owned arcs from some `b ∈ B` to `v`
   with `c(Q_v) ≤ 2Γ`, and some walk `W` from `r` to `b` in `F` has `ℓ(W) + ℓ(Q_v) ≤ A(v)`: the
   extension arrives by `A(v)` after an actually paid prefix.

**Formalization Note.** `Γ = 0` is included: then `c(Q_v) ≤ 2Γ = 0`, the zero-cost case of the
lemma. "`A(v) ≤ a(b) + ℓ(Q)` with `a(b) = dist_F(r,b)`" is stated for every `F`-walk to `b`
(boundary vertices with infinite label impose nothing). The comparison ranges over all owned
walks of list-cost `≤ Γ`, which contain the paper's paths. The region structure of `E_R` and `B` is
not assumed. "`O(n²)` states" describes the construction and is not stated. -/
theorem lemma_3_2 :
    ∃ alg : Net × List ℕ × List ℕ × List ℕ × ℕ × ℚ → List (Bool × ℚ × List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encArrIn encArrOut alg) ∧
      ∀ (G : Net) (ER B F : List ℕ) (r : ℕ) (Γ : ℚ), G.WF → r < G.n → 0 ≤ Γ →
        (alg (G, ER, B, F, r, Γ)).length = G.n ∧
        ∀ v < G.n,
          (∀ b ∈ B, ∀ Q : List ℕ, IsWalk G b v Q → (∀ e ∈ Q, e ∈ ER) → lcost G Q ≤ Γ →
            ∀ W : List ℕ, IsWalk G r b W → (∀ e ∈ W, e ∈ F) →
              ((alg (G, ER, B, F, r, Γ)).getD v (false, 0, [])).1 = true ∧
              ((alg (G, ER, B, F, r, Γ)).getD v (false, 0, [])).2.1 ≤ plen G W + plen G Q) ∧
          (((alg (G, ER, B, F, r, Γ)).getD v (false, 0, [])).1 = true →
            ∃ b ∈ B, IsSPath G b v ((alg (G, ER, B, F, r, Γ)).getD v (false, 0, [])).2.2 ∧
              (∀ e ∈ ((alg (G, ER, B, F, r, Γ)).getD v (false, 0, [])).2.2, e ∈ ER) ∧
              lcost G ((alg (G, ER, B, F, r, Γ)).getD v (false, 0, [])).2.2 ≤ 2 * Γ ∧
              ∃ W : List ℕ, IsWalk G r b W ∧ (∀ e ∈ W, e ∈ F) ∧
                plen G W + plen G ((alg (G, ER, B, F, r, Γ)).getD v (false, 0, [])).2.2 ≤
                  ((alg (G, ER, B, F, r, Γ)).getD v (false, 0, [])).2.1) := by sorry

end LCPlanarSteiner
