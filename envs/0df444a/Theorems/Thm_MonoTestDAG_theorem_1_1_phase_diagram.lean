-- Prove2me | Theorems.Thm_MonoTestDAG_theorem_1_1_phase_diagram
-- name    : MonoTestDAG.theorem_1_1_phase_diagram
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:11:01.425874+00:00
-- url     : https://prove2.me/theorems/7dc5696c-a33e-4281-934b-769b51698d75
-- title:
--   Theorem 1.1 — query complexity $n^{u(c,d)\pm o(1)}$ for every pair of reachability exponents
-- statement:
--   Fix constants $1\le c\le d\le2$ and define
--   $$
--   u(c,d):=\min\Bigl\{\tfrac12,\ \tfrac c3,\ \tfrac{c+d}2-1\Bigr\}.
--   $$
--   Write $m$ for the number of edges of the transitive reduction and $\ell$ for the number of edges of the transitive closure of an $n$-vertex DAG.
--
--   1. For every fixed $\varepsilon\in(0,1)$, every family of $n$-vertex DAGs with $m=n^{c+o(1)}$ and $\ell=n^{d+o(1)}$ admits a non-adaptive one-sided $\varepsilon$-tester using $O_\varepsilon(n^{u(c,d)+o(1)})$ queries.
--   2. For every sufficiently small fixed $\varepsilon>0$, there is a family of $n$-vertex DAGs with $m=n^{c+o(1)}$ and $\ell=n^{d+o(1)}$ on which every randomized non-adaptive $\varepsilon$-tester, even with two-sided error, requires $n^{u(c,d)-o(1)}$ queries.
--
--   The two parts determine the non-adaptive query complexity up to a factor $n^{o(1)}$ at every pair of exponents.
--
--   **Formalization Note.** Part 1 reads: for all $\varepsilon\in(0,1)$, $1\le c\le d\le2$ and $\delta>0$ there are $\nu>0$ and $N_0$ such that every DAG with $n\ge N_0$, $n^{c-\nu}\le m\le n^{c+\nu}$ and $n^{d-\nu}\le\ell\le n^{d+\nu}$ has a one-sided $\varepsilon$-tester with at most $n^{u(c,d)+\delta}$ queries on every seed. Part 2 reads: for all $1\le c\le d\le2$ there is $\varepsilon_0>0$ such that for all $\varepsilon\in(0,\varepsilon_0]$, $\delta>0$ and $N_0$ there is a DAG with $n\ge N_0$, $n^{c-\delta}\le m\le n^{c+\delta}$ and $n^{d-\delta}\le\ell\le n^{d+\delta}$ on which every two-sided $\varepsilon$-tester making at most $q$ queries on every seed has $n^{u(c,d)-\delta}\le q$.
--
--   Differences from the source:
--   - encoding: families of DAGs with exponents n^{c+o(1)}, n^{d+o(1)} and bounds n^{u±o(1)}, O_ε → the uniform ν, δ, N₀ form in the Formalization Note, with the O_ε constant absorbed by n^δ for n ≥ N₀; reason: equivalent to the family form by a diagonal argument; the proof states this equivalence on p.37
--   - encoding: m, ℓ of a DAG that may contain transitive edges → `numTR E` and `numTC E`, computed from reachability; reason: m counts edges of the transitive reduction, as Theorem 1.1's preamble says
--   - encoding: randomized non-adaptive tester → the structure `Tester`: arbitrary probability space in `Type`, query set a function of the seed, decision a function of the seed and the answers on that set, acceptance event of each input measurable in the seed; reason: the paper's definition in §2.4; a universe-0 probability space loses no tester of the paper; measurability only makes the acceptance probability defined
--   - encoding: one-sided error: "always accepts" / "with probability 1" → acceptance probability 1; reason: §2.4 prints both; probability 1 is the form in the completeness requirement
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Theorem 1.1, p.1

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_HasExponents
import Definitions.Def_MonoTestDAG_rate

namespace MonoTestDAG

/-- **Theorem 1.1 (Query complexity for every pair of reachability exponents).** Fix constants
`1 ≤ c ≤ d ≤ 2` and define `u(c, d) := min{1/2, c/3, (c + d)/2 − 1}`.
(i) For every fixed `ε ∈ (0, 1)`, every family of `n`-vertex DAGs satisfying `m = n^{c+o(1)}` and
`ℓ = n^{d+o(1)}` admits a non-adaptive one-sided `ε`-tester using `O_ε(n^{u(c,d)+o(1)})` queries.
(ii) For every sufficiently small fixed `ε > 0`, there is a family of `n`-vertex DAGs satisfying
`m = n^{c+o(1)}` and `ℓ = n^{d+o(1)}` on which every randomized non-adaptive `ε`-tester, even with
two-sided error, requires `n^{u(c,d)−o(1)}` queries.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Theorem 1.1, p.1.

**Formalization Note.** `m` is the number of edges of the transitive reduction and `ℓ` of the
transitive closure, both computed from reachability; the DAG `E` may contain transitive edges. The
families and their `o(1)`s are in uniform form, equivalent to the family form by a diagonal
argument: in (i), for every `δ > 0` the bound `n^{u+δ}` holds for all DAGs with `n ≥ N₀` whose
exponents are within `ν` of `(c, d)`, the `O_ε` constant being absorbed by `n^δ` (`ν`, `N₀` depend
on `ε, c, d, δ`); in (ii), for every `δ > 0` and `N₀` there is a DAG with `n ≥ N₀` whose exponents
are within `δ` of `(c, d)` and on which every tester making at most `q` queries on every seed has
`n^{u−δ} ≤ q`. A tester makes worst-case queries over an arbitrary probability space (see
`Tester`). -/
theorem theorem_1_1_phase_diagram :
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ c d : ℝ, 1 ≤ c → c ≤ d → d ≤ 2 → ∀ δ : ℝ, 0 < δ →
      ∃ ν : ℝ, 0 < ν ∧ ∃ N₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (E : V → V → Prop),
        IsDAG E → N₀ ≤ Fintype.card V → HasExponents E c d ν →
        ∃ T : Tester V, IsOneSidedTester E ε T ∧
          T.QueriesAtMost ((Fintype.card V : ℝ) ^ (rate c d + δ))) ∧
    (∀ c d : ℝ, 1 ≤ c → c ≤ d → d ≤ 2 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ δ : ℝ, 0 < δ → ∀ N₀ : ℕ,
        ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (E : V → V → Prop),
          N₀ ≤ Fintype.card V ∧ 1 ≤ Fintype.card V ∧ IsDAG E ∧ HasExponents E c d δ ∧
          ∀ (T : Tester V) (q : ℝ), IsTwoSidedTester E ε T → T.QueriesAtMost q →
            (Fintype.card V : ℝ) ^ (rate c d - δ) ≤ q) := by sorry

end MonoTestDAG
