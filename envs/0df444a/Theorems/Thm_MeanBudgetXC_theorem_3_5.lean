-- Prove2me | Theorems.Thm_MeanBudgetXC_theorem_3_5
-- name    : MeanBudgetXC.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:34.320079+00:00
-- url     : https://prove2.me/theorems/fe6b72ee-09d9-43e2-8d07-907da0082136
-- title:
--   Theorem 3.5, Eq. (6) — objective bound for nonintegral RLT vertices
-- statement:
--   Let $2\le d\le N$, let $q\ge0$ be a pair array and let $p$ satisfy (5): $T_i(q)\le p_i\le\deg_q(i)$ for every $i$. Put $P_{\mathrm{tot}}=\sum_ip_i$ and $F_S(p,q)=p(S)-q(E(S))$.
--
--   1. For every nonintegral vertex $(x,y)$ of $R_{N,d}$, $J_{p,q}(x,y)\le P_{\mathrm{tot}}/2$.
--   2. Consequently,
--   $$\max_{(x,y)\in R_{N,d}}J_{p,q}(x,y)\le\max\Big\{P_{\mathrm{tot}}/2,\ \max_{|S|=d}F_S(p,q)\Big\}.$$
--
--   The bound applies in particular to the minimum lift $p=T(q)$. At budget two it gives $P_{\mathrm{tot}}/2\le1$, as the empty-atom constraints require.
--
--   **Formalization Note** The maximum over $R_{N,d}$ is stated pointwise: every $(x,y)\in R_{N,d}$ has objective at most $P_{\mathrm{tot}}/2$ or at most $F_S(p,q)$ for some $d$-set $S$.
--
--   Differences from the source:
--   - encoding: The vertex set is $[N]$ → it is an arbitrary finite type $V$ with $N=|V|$; reason: every finite type is in bijection with $[N]$, so no instance changes
--   - encoding: vertex of the polytope $R_{N,d}$ → extreme point (`Set.extremePoints`); reason: for a polytope the two notions coincide
--   - reading: nonintegral vertex → some coordinate of $x$ or $y$ is not an integer; reason: the paper does not spell this out, and it is the plain meaning; on $R_{N,d}$ integral $x$ forces integral $y$, so reading it on $x$ alone gives the same vertices
--   - encoding: a bound on the maximum over $R_{N,d}$ in (6) → a pointwise bound at every $(x,y)\in R_{N,d}$ with a disjunction; reason: the maximum over a compact set is attained and the inner maximum is over a finite nonempty family, so the two forms are equivalent
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Theorem 3.5, display (6), p.13

import Mathlib
import Definitions.Def_MeanBudgetXC_topSum
import Definitions.Def_MeanBudgetXC_edgeMass
import Definitions.Def_MeanBudgetXC_rltPolytope
import Definitions.Def_MeanBudgetXC_rltObjective

namespace MeanBudgetXC

/-- **Theorem 3.5** (Objective bound for nonintegral RLT vertices), with display (6)
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 3.4, p.13). Let `2 ≤ d ≤ N`, `q ≥ 0`, and
let `p` satisfy (5): `T_i(q) ≤ p_i ≤ deg_q(i)`. For every nonintegral vertex `(x, y)` of
`R_{N,d}`, `J_{p,q}(x, y) ≤ P_tot/2`. Consequently
`max_{(x,y) ∈ R_{N,d}} J_{p,q}(x, y) ≤ max{P_tot/2, max_{|S|=d} F_S(p, q)}` with
`F_S(p, q) = p(S) − q(E(S))`.

**Formalization Note** "Nonintegral" means that some coordinate of `(x, y)` is not an integer;
"vertex" is an extreme point. Display (6) is stated pointwise: every `(x, y) ∈ R_{N,d}` has
`J_{p,q}(x, y) ≤ P_tot/2` or `J_{p,q}(x, y) ≤ F_S(p, q)` for some `d`-set `S`, which is equivalent
to the bound on the maximum (the maximum over the compact `R_{N,d}` is attained, and the inner
maximum is over a finite family). The vertex set is a generic finite type `V` with `N = card V`. -/
theorem theorem_3_5 {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd2 : 2 ≤ d)
    (hdN : d ≤ Fintype.card V) (p : V → ℝ) (q : Pair V → ℝ) (hq : ∀ e, 0 ≤ q e)
    (h5 : ∀ i, topSum d q i ≤ p i ∧ p i ≤ ∑ j, entry q i j) :
    (∀ xy ∈ Set.extremePoints ℝ (rltPolytope V d),
        ¬ ((∀ i, ∃ n : ℤ, xy.1 i = n) ∧ ∀ e, ∃ n : ℤ, xy.2 e = n) →
          rltObjective p q xy ≤ (∑ i, p i) / 2) ∧
      ∀ xy ∈ rltPolytope V d, rltObjective p q xy ≤ (∑ i, p i) / 2 ∨
        ∃ S : Finset V, S.card = d ∧ rltObjective p q xy ≤ ∑ i ∈ S, p i - edgeMass q S := by sorry

end MeanBudgetXC
