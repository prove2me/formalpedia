-- Prove2me | Theorems.Thm_MonoApport_Flow_extreme_points_eq_integer
-- name    : MonoApport.Flow.extreme_points_eq_integer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:30.202543+00:00
-- url     : https://prove2.me/theorems/7fd8c3db-ff5e-41e5-8db2-afff03666d73
-- title:
--   §5, p. 19 — the extreme points of (1)-(4) are exactly its integer feasible solutions
-- statement:
--   Let $p\in\mathbb N^n$ be a vector of positive populations and $L\ge1$ a number of seats, $K(p,L)$ the feasible region of the linear program (1)–(4) (each seat goes to exactly one unit of mass, the prefix sums of each state lie between $\lfloor tp_i/P\rfloor$ and $\lceil tp_i/P\rceil$, and $x\ge0$), and $\mathcal E(p,L)$ its set of extreme points.
--
--   **Claim (§5, p. 19).** Since every feasible solution of (1)–(4) lies in the unit hypercube, Lemma 3 implies
--   $$\mathcal E(p,L)=\{x\in K(p,L): x(i,t)\in\mathbb Z\ \text{for all } i\in[n],\ t\in[L]\}.$$
--
--   This identifies $\mathcal E(p,L)$ with the seat sequences that are quota-compliant at every house size up to $L$, the form in which the set enters Theorem 3.
--
--   Differences from the source:
--   - encoding: variables x(i, t) for seats t ∈ [L] = {1, …, L}, with prefix sums over ℓ = 1, …, t bounded by ⌊t pᵢ/P⌋ and ⌈t pᵢ/P⌉ → x : Fin n → Fin L → ℝ, column t : Fin L standing for seat t + 1; the bounds at column t are ⌊(t + 1) pᵢ/P⌋ and ⌈(t + 1) pᵢ/P⌉ on the sum over columns ℓ ≤ t; reason: 0-indexed relabelling of the seats; no instance changes
-- source:
--   Cembrano, Correa, Schmidt-Kraepelin, Tsigonias-Dimitriadis & Verdugo, New Combinatorial Insights for Monotone Apportionment, arXiv:2410.23869v1, §5, p. 19 (remark after Lemma 3)

import Mathlib
import Definitions.Def_MonoApport_Flow_Setting

namespace MonoApport.Flow

/-- §5, p. 19: the extreme points of (1)-(4) are exactly its integer feasible solutions. -/
theorem extreme_points_eq_integer {n : ℕ} (p : Fin n → ℕ) (hp : IsPop p) (L : ℕ) (hL : 0 < L) :
    calE p L = {x | x ∈ K p L ∧ ∀ (i : Fin n) (t : Fin L), ∃ z : ℤ, x i t = z} := by sorry

end MonoApport.Flow
