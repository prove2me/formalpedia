-- Prove2me | Theorems.Thm_MonoApport_Flow_lemma_3
-- name    : MonoApport.Flow.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:41.365211+00:00
-- url     : https://prove2.me/theorems/316a8a8e-790b-47e1-b5c1-3212b3caf0e3
-- title:
--   Lemma 3, p. 19 — for every instance (p, H) the linear program (1)-(4) is integral
-- statement:
--   Let $p\in\mathbb N^n$ be a vector of positive populations with total $P$, and $L\ge1$ a number of seats. Let $K(p,L)$ be the feasible region of the linear program
--   $$\sum_{i=1}^n x(i,t)=1,\qquad \Big\lfloor\tfrac{tp_i}{P}\Big\rfloor\le\sum_{\ell=1}^t x(i,\ell)\le\Big\lceil\tfrac{tp_i}{P}\Big\rceil,\qquad x(i,t)\ge0\qquad(i\in[n],\ t\in[L]),$$
--   constraints (1)–(4), and $\mathcal E(p,L)$ its set of extreme points.
--
--   **Lemma 3.** For every instance $(p,L)$, the linear program (1)-(4) is integral: every extreme point $x\in\mathcal E(p,L)$ has integer coordinates $x(i,t)\in\mathbb Z$.
--
--   Integrality makes the extreme points of (1)-(4) exactly its 0/1 solutions, which encode seat-by-seat assignments respecting the quota bounds at every intermediate house size.
--
--   Differences from the source:
--   - reading: the linear program (1)-(4) is integral → every extreme point of the feasible region K(p, L) has integer coordinates; reason: (1)-(4) has no objective and its feasible region is a bounded polyhedron, so integrality of the LP means integrality of its vertices; for a polytope this is equivalent to every linear objective attaining its optimum at an integer point
--   - encoding: variables x(i, t) for seats t ∈ [L] = {1, …, L}, with prefix sums over ℓ = 1, …, t bounded by ⌊t pᵢ/P⌋ and ⌈t pᵢ/P⌉ → x : Fin n → Fin L → ℝ, column t : Fin L standing for seat t + 1; the bounds at column t are ⌊(t + 1) pᵢ/P⌋ and ⌈(t + 1) pᵢ/P⌉ on the sum over columns ℓ ≤ t; reason: 0-indexed relabelling of the seats; no instance changes
-- source:
--   Cembrano, Correa, Schmidt-Kraepelin, Tsigonias-Dimitriadis & Verdugo, New Combinatorial Insights for Monotone Apportionment, arXiv:2410.23869v1, Lemma 3, p. 19 (proof §C.3, pp. 39–41)

import Mathlib
import Definitions.Def_MonoApport_Flow_Setting

namespace MonoApport.Flow

/-- Lemma 3 (p. 19): for every instance `(p, H)`, the linear program (1)-(4) is integral: every
extreme point of its feasible region has integer coordinates. -/
theorem lemma_3 {n : ℕ} (p : Fin n → ℕ) (hp : IsPop p) (L : ℕ) (hL : 0 < L) :
    ∀ x ∈ calE p L, ∀ (i : Fin n) (t : Fin L), ∃ z : ℤ, x i t = z := by sorry

end MonoApport.Flow
