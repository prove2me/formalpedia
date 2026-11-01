-- Prove2me | Theorems.Thm_MinSharing_lemma_3_8
-- name    : MinSharing.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:03.905448+00:00
-- url     : https://prove2.me/theorems/ac57cf7a-099f-4e58-ab8f-31811f41bfa4
-- title:
--   Lemma 3.8 — two agents: $|\mathcal G_v|\le 3m\cdot3^{D_v}$, enumerable in $O(m\cdot3^{D_v})$ operations on ratio-sorted input
-- statement:
--   Consider two agents and $m\ge1$ objects with a real valuation matrix $v$.
--
--   1. The number of fPO graphs satisfies
--   $$|\mathcal G_v|\le 3m\cdot 3^{D_v}.$$
--   2. There are a real-RAM program $R$, a report position $p$ and a constant $K>0$ such that, for every $m\ge1$ and every $v$ in which the objects $o$ with $v_{1,o}v_{2,o}>0$ are listed in monotone (non-increasing or non-decreasing) order of $|v_{1,o}|/|v_{2,o}|$, the program started on the instance memory of $v$ enumerates $\mathcal G_v$ within
--   $$K\cdot m\cdot 3^{D_v}$$
--   steps: it halts within that many steps, every graph in its graph region at the report position is in $\mathcal G_v$, and every graph of $\mathcal G_v$ appears there.
--
--   This is the base case of the agent-by-agent enumeration of Proposition 3.7.
--
--   Differences from the source:
--   - encoding: every count and step bound for m objects → stated for m ≥ 1; reason: the paper writes [m] = {1,…,m}; at m = 0 the set G_v = {∅} has one element while the printed bounds are 0
--   - encoding: D_v → the integer degeneracy v, which can be −1, with 3^(…D_v) a real power with integer exponent; reason: D_v + 1 counts objects and can be 0 (e.g. n = 2, m = 1, v = (1; 0)); no truncation at 0
--   - reading: G_v can be enumerated using O(f) operations → EnumeratesWithin: R halts within K·f steps; whenever the program counter is at a fixed report position p before halting, the graph region of memory holds a graph of the set, and every graph of the set is held there at some such step; reason: writing every graph out in full would make Lemma 3.8(b) false (2m + 1 graphs with Θ(m) edges each for non-degenerate pure goods); the proof says consecutive graphs differ only in the objects of A=(t) and A=(t′), p.17
--   - reading: enumerated using O(m·3^{D_v}) operations → number of executed instructions of one program of the published real RAM (SmaleNinth.RAMProgram, unit cost, exact real arithmetic) bounded by K times the expression, with the output correct; reason: the paper counts arithmetic operations and comparisons on real numbers (multiplicative Bellman–Ford, App. A p.31; constant-size LPs, p.14)
--   - reading: the objects o with v_{1,o}·v_{2,o} > 0 are ordered by the ratio |v_{1,o}|/|v_{2,o}| → IsRatioSorted v: among those objects, the ratio is monotone in the object index, non-increasing or non-decreasing; the order is a precondition on the input; reason: the page does not fix the direction (the proof of Theorem 3.3, p.13, sorts in descending order), so both directions are admitted
--   - encoding: agents [n] = {1,…,n}, objects [m] = {1,…,m} → Fin n, Fin m (paper index = Lean index + 1); reason: Lean convention; same instances
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, Lemma 3.8, p.16 (proof pp.16–17)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MinSharing_Setting
import Definitions.Def_MinSharing_RAMInterface

set_option autoImplicit false

namespace MinSharing

open SmaleNinth

/-- **Lemma 3.8** (Sandomirskiy, Segal-Halevi, arXiv:1908.01669v3, p.16). For an instance `v`
with `2` agents and `m` objects: (a) the total number of graphs in `G_v` is at most `3m · 3^{D_v}`.
(b) If all the objects `o` with `v₁,ₒ · v₂,ₒ > 0` are ordered by the ratio `|v₁,ₒ|/|v₂,ₒ|`, then `G_v`
can be enumerated using `O(m · 3^{D_v})` operations.

**Formalization Note** `m ≥ 1` (for `m = 0`, `G_v = {∅}` has one element and the bounds are `0`).
`D_v` is the integer `degeneracy v`, which can be `−1`; `3^{D_v}` is a real power with integer
exponent. `G_v` is a finite set (`Set.ncard`). (b): one program `R` of the published real RAM, a
report position `p` and a constant `K > 0`, chosen before `m` and `v`; on the input memory
`instanceMem v` of every ratio-sorted instance (`IsRatioSorted`, either direction) `R` halts
within `K · m · 3^{D_v}` steps, and the graphs held in the graph region whenever the program counter
is at `p` before halting are exactly the graphs of `G_v` (`EnumeratesWithin`). -/
theorem lemma_3_8 :
    (∀ m : ℕ, 1 ≤ m → ∀ v : Fin 2 → Fin m → ℝ,
      ((fpoGraphs v).ncard : ℝ) ≤ 3 * m * (3 : ℝ) ^ degeneracy v) ∧
    ∃ R : RAMProgram, ∃ p : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ m : ℕ, 1 ≤ m → ∀ v : Fin 2 → Fin m → ℝ, IsRatioSorted v →
        EnumeratesWithin 2 m 2 R p (instanceMem v) (fpoGraphs v)
          (K * m * (3 : ℝ) ^ degeneracy v) := by sorry

end MinSharing
