-- Prove2me | Theorems.Thm_OAI_RandomKSAT_capped_coordinate_omission
-- name    : OAI.RandomKSAT.capped_coordinate_omission
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:00:59.10698+00:00
-- url     : https://prove2.me/theorems/d44d6d87-91ab-443d-9a71-80cc63ffc696
-- title:
--   Efron–Stein-type bound for the variance of the capped first failure time of random $k$-SAT
-- statement:
--   Fix natural numbers $n$ and $k$, and write $[n]=\{0,1,\dots,n-1\}$ for the set of Boolean variables. An *assignment* is a map $a:[n]\to\{\mathrm T,\mathrm F\}$. A *clause of width $k$* is a pair $c=(V,\beta)$ of a set $V\subseteq[n]$ with $|V|=k$ and a sign map $\beta:V\to\{\mathrm T,\mathrm F\}$; the assignment $a$ *satisfies* $c$ if $a(v)=\beta(v)$ for at least one $v\in V$. Let $\mathcal C_{n,k}$ be the finite set of all such clauses; it has $\binom nk2^k$ elements.
--
--   A *stream* is an infinite sequence $\omega=(\omega_0,\omega_1,\omega_2,\dots)$ of clauses from $\mathcal C_{n,k}$. Write $\mathrm{SAT}_m(\omega)$ if some single assignment satisfies all of $\omega_0,\dots,\omega_{m-1}$ (for $m=0$ this always holds). The *first failure time* of $\omega$ is $\tau(\omega)=\min\{m\in\mathbb N:\ \mathrm{SAT}_m(\omega)\text{ fails}\}\in\mathbb N\cup\{\infty\}$, with $\tau(\omega)=\infty$ if every prefix is satisfiable. Let $\mathbb P_{n,k}$ be the law on streams under which $\omega_0,\omega_1,\dots$ are independent and each is uniformly distributed on $\mathcal C_{n,k}$; it is a probability measure as soon as $k\le n$, so that clauses exist.
--
--   For a real number $B$ let $N=\lfloor Bn\rfloor$ if $Bn\ge0$ and $N=0$ otherwise, and let $T_B(\omega)=\min(\tau(\omega),N)$, viewed as a real number (the first failure time capped at $N$). For a tuple $\mathbf c=(c_0,\dots,c_{N-1})\in\mathcal C_{n,k}^N$ and an index $i\in\{0,\dots,N-1\}$ define
--
--   - $F(\mathbf c)=\#\{m\in\{0,\dots,N-1\}:\ \text{the clauses } c_j \text{ with } j<m \text{ have a common satisfying assignment}\}$,
--   - $F^{(i)}(\mathbf c)=\#\{m\in\{0,\dots,N-1\}:\ \text{the clauses } c_j \text{ with } j<m,\ j\neq i, \text{ have a common satisfying assignment}\}$.
--
--   So $F^{(i)}$ is computed with the clause $c_i$ deleted, and it does not depend on $c_i$.
--
--   **Theorem.** If $k\le n$, then for every $B\in\mathbb R$
--   $$
--   \operatorname{Var}_{\mathbb P_{n,k}}(T_B)\le\sum_{i=0}^{N-1}\frac{1}{|\mathcal C_{n,k}|^N}\sum_{\mathbf c\in\mathcal C_{n,k}^N}\big(F^{(i)}(\mathbf c)-F(\mathbf c)\big)^2 .
--   $$
--   Each inner average is $\mathbb E\big[(F^{(i)}-F)^2\big]$ for $N$ independent uniformly random clauses.
--
--   The variance of the capped first failure time is therefore bounded by the total mean squared effect of deleting one clause at a time. This reduces the upper bound on the variance of $T_B$ to estimating, position by position, how much the number of satisfiable prefixes can change when a single clause is removed.
--
--   **Formalization Note** $T_B$ is `T B`, i.e. `(min (firstFailure ω) (cap n B)).toNat` with `cap n B` the natural floor `⌊B * n⌋₊`. The variance is Mathlib's `ProbabilityTheory.variance` under `streamLaw n k`. On the right-hand side the average is `favg` over `Fin (cap n B) → Clause n k`, $F$ is `finiteTime` and $F^{(i)}$ is `omittedTime i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FiniteVariance.lean#L184-L199

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.capped_coordinate_omission {n k : ℕ} (hkn : k ≤ n) (B : ℝ) :
    ProbabilityTheory.variance (T B : Stream n k → ℝ) (streamLaw n k) ≤
      ∑ i : Fin (cap n B), favg (fun cs : Fin (cap n B) → Clause n k =>
        (omittedTime i cs - finiteTime cs)^2) := by sorry
