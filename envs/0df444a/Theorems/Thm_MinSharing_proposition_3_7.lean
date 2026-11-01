-- Prove2me | Theorems.Thm_MinSharing_proposition_3_7
-- name    : MinSharing.proposition_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:13.966926+00:00
-- url     : https://prove2.me/theorems/347c7869-1ecc-42aa-af8b-37e588b6f229
-- title:
--   Proposition 3.7 with (3.1) — for fixed $n$, $\mathcal G_v$ is enumerable in $O(3^{n(n-1)D_v/2}m^{n(n-1)/2+2})$ operations and $|\mathcal G_v|\le3^{(1+D_v)n(n-1)/2}m^{n(n-1)/2}$
-- statement:
--   Fix $n\ge2$ agents. For valuation matrices $v\in\mathbb R^{n\times m}$, $m\ge1$:
--
--   1. there are a real-RAM program $R$, a report position $p$ and a constant $K>0$ (depending on $n$) such that for every $m\ge1$ and every $v$ the program, started on the instance memory of $v$, enumerates the set $\mathcal G_v$ of fPO graphs within
--   $$K\cdot 3^{\frac{n(n-1)}2\cdot D_v}\cdot m^{\frac{n(n-1)}2+2}$$
--   steps;
--   2. in particular, for every $C>0$ there are $K'>0$ and $d$ such that the same program enumerates $\mathcal G_v$ within $K'm^d$ steps whenever $D_v\le C\log m$ (strongly polynomial time for logarithmic degeneracy);
--   3. the number of fPO graphs satisfies
--   $$|\mathcal G_v|\le 3^{(1+D_v)\frac{n(n-1)}2}\cdot m^{\frac{n(n-1)}2}. \tag{3.1}$$
--
--   The polynomial bound (3.1) on the number of consumption graphs of fPO allocations is the structural fact behind the algorithm of Theorem 3.6(a), whose first phase is this enumeration.
--
--   Differences from the source:
--   - encoding: every count and step bound for m objects → stated for m ≥ 1; reason: the paper writes [m] = {1,…,m}; at m = 0 the set G_v = {∅} has one element while the printed bounds are 0
--   - encoding: D_v → the integer degeneracy v, which can be −1, with 3^(…D_v) a real power with integer exponent; reason: D_v + 1 counts objects and can be 0 (e.g. n = 2, m = 1, v = (1; 0)); no truncation at 0
--   - reading: G_v can be enumerated using O(f) operations → EnumeratesWithin: R halts within K·f steps; whenever the program counter is at a fixed report position p before halting, the graph region of memory holds a graph of the set, and every graph of the set is held there at some such step; reason: writing every graph out in full would make Lemma 3.8(b) false (2m + 1 graphs with Θ(m) edges each for non-degenerate pure goods); the proof says consecutive graphs differ only in the objects of A=(t) and A=(t′), p.17
--   - reading: enumerated using O(3^{n(n−1)/2·D_v}·m^{n(n−1)/2+2}) operations → number of executed instructions of one program of the published real RAM (SmaleNinth.RAMProgram, unit cost, exact real arithmetic) bounded by K times the expression, with the output correct; reason: the paper counts arithmetic operations and comparisons on real numbers (multiplicative Bellman–Ford, App. A p.31; constant-size LPs, p.14)
--   - reading: strongly-polynomial time → for every C > 0 there are K′ > 0 and d with a K′·m^d bound on the number of real-RAM instructions of the same program; reason: the paper uses strongly polynomial for an operation count that is polynomial and independent of the magnitudes of the entries, in contrast with the weakly polynomial LP method (p.9)
--   - encoding: log(m) → Real.log m (natural logarithm); reason: the clause is for every C > 0, so the base is immaterial
--   - encoding: n(n−1)/2 → the natural number n * (n - 1) / 2; reason: n(n−1) is even, so the division is exact
--   - encoding: "for every fixed number of agents n" → R, p and K are chosen after n and before m and v; reason: the O-constant depends on the fixed n
--   - encoding: agents [n] = {1,…,n}, objects [m] = {1,…,m} → Fin n, Fin m (paper index = Lean index + 1); reason: Lean convention; same instances
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, Proposition 3.7 and (3.1), p.15 (proof via Lemmas 3.8–3.9, pp.16–18)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MinSharing_Setting
import Definitions.Def_MinSharing_RAMInterface

set_option autoImplicit false

namespace MinSharing

open SmaleNinth

/-- **Proposition 3.7** with (3.1) (Sandomirskiy, Segal-Halevi, arXiv:1908.01669v3, p.15). For
every fixed number of agents `n ≥ 2`, the set of all fPO graphs `G_v := {CG_z : z is fPO for v}`
can be enumerated using `O(3^{n(n−1)/2·D_v} · m^{n(n−1)/2+2})` operations. In particular, for `v`
with logarithmic degeneracy (`D_v ≤ C · log(m)`), the algorithm runs in strongly-polynomial time.
The total number of graphs in `G_v` satisfies `|G_v| ≤ 3^{(1+D_v)·n(n−1)/2} · m^{n(n−1)/2}` (3.1).

**Formalization Note** For each `n ≥ 2`: one program `R` of the published real RAM, a report
position `p` and a constant `K > 0`, chosen before `m` and `v`, enumerate `G_v`
(`EnumeratesWithin`, graph region on all `n` agent rows) on the input memory `instanceMem v`
within `K · 3^{n(n−1)/2·D_v} · m^{n(n−1)/2+2}` steps, for every `m ≥ 1` and every real `v`. The
"in particular" clause is about the same `R`: for every `C > 0` there are `K' > 0` and `d` such
that `R` enumerates within `K' · m^d` steps whenever `D_v ≤ C · log m` (natural logarithm;
strongly polynomial = a number of real-arithmetic operations polynomial in `m`, independent of the
magnitudes of the entries). `D_v` is an integer (possibly `−1`), `n(n−1)/2` is the natural number
`n * (n - 1) / 2`, and the powers of `3` have integer exponents. (3.1) is for `m ≥ 1`. -/
theorem proposition_3_7 (n : ℕ) (hn : 2 ≤ n) :
    (∃ R : RAMProgram, ∃ p : ℕ, ∃ K : ℝ, 0 < K ∧
      (∀ m : ℕ, 1 ≤ m → ∀ v : Fin n → Fin m → ℝ,
        EnumeratesWithin n m n R p (instanceMem v) (fpoGraphs v)
          (K * (3 : ℝ) ^ (((n * (n - 1) / 2 : ℕ) : ℤ) * degeneracy v) *
            (m : ℝ) ^ (n * (n - 1) / 2 + 2))) ∧
      ∀ C : ℝ, 0 < C → ∃ K' : ℝ, ∃ d : ℕ, 0 < K' ∧
        ∀ m : ℕ, 1 ≤ m → ∀ v : Fin n → Fin m → ℝ, (degeneracy v : ℝ) ≤ C * Real.log m →
          EnumeratesWithin n m n R p (instanceMem v) (fpoGraphs v) (K' * (m : ℝ) ^ d)) ∧
    ∀ m : ℕ, 1 ≤ m → ∀ v : Fin n → Fin m → ℝ,
      ((fpoGraphs v).ncard : ℝ) ≤
        (3 : ℝ) ^ ((1 + degeneracy v) * ((n * (n - 1) / 2 : ℕ) : ℤ)) *
          (m : ℝ) ^ (n * (n - 1) / 2) := by sorry

end MinSharing
