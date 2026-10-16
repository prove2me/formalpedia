-- Prove2me | Theorems.Thm_OAI_RandomKSAT_natH_mass_bound
-- name    : OAI.RandomKSAT.natH_mass_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:57:48.065283+00:00
-- url     : https://prove2.me/theorems/7ebaefd4-0692-4b10-9c87-eb1f765205dc
-- title:
--   Geometric bound on the point probabilities of the first unsatisfiability time
-- statement:
--   Fix natural numbers $n$ and $k$, and write $[n]=\{0,1,\dots,n-1\}$ for the set of Boolean variables. An *assignment* is a map $a:[n]\to\{\mathrm T,\mathrm F\}$. A *clause of width $k$* is a pair $c=(V,\beta)$ of a set $V\subseteq[n]$ with $|V|=k$ and a sign map $\beta:V\to\{\mathrm T,\mathrm F\}$; the assignment $a$ *satisfies* $c$ if $a(v)=\beta(v)$ for at least one $v\in V$. Let $\mathcal C_{n,k}$ be the finite set of all such clauses; it has $\binom nk2^k$ elements.
--
--   A *stream* is an infinite sequence $\omega=(\omega_0,\omega_1,\omega_2,\dots)$ of clauses from $\mathcal C_{n,k}$. Write $\mathrm{SAT}_m(\omega)$ if some single assignment satisfies all of $\omega_0,\dots,\omega_{m-1}$ (for $m=0$ this always holds). The *first failure time* of $\omega$ is $\tau(\omega)=\min\{m\in\mathbb N:\ \mathrm{SAT}_m(\omega)\text{ fails}\}\in\mathbb N\cup\{\infty\}$, with $\tau(\omega)=\infty$ if every prefix is satisfiable. Let $\mathbb P_{n,k}$ be the law on streams under which $\omega_0,\omega_1,\dots$ are independent and each is uniformly distributed on $\mathcal C_{n,k}$; it is a probability measure as soon as $k\le n$, so that clauses exist. Finally let $\bar\tau(\omega)\in\mathbb N$ equal $\tau(\omega)$ when $\tau(\omega)<\infty$ and $0$ when $\tau(\omega)=\infty$.
--
--   **Theorem.** If $1\le k\le n$, then for every $m\in\mathbb N$
--   $$
--   \mathbb P_{n,k}\big(\bar\tau=m\big)\le\frac{2^n}{1-2^{-k}}\,\big(1-2^{-k}\big)^m .
--   $$
--
--   The point probabilities of the first failure time therefore decay geometrically with ratio $1-2^{-k}$. Summing these bounds against powers of $m$ shows that $\bar\tau$, which is the real-valued first failure time appearing in the variance estimates for random $k$-SAT, has finite moments of all orders; in particular its mean and variance are finite.
--
--   **Formalization Note** The left-hand side is the real number obtained by evaluating at $\{m\}$ the push-forward of `streamLaw n k` under `fun ω => (firstFailure ω).toNat`. `ENat.toNat` sends $\infty$ to $0$, which is why $\bar\tau$ reads $\infty$ as $0$. The hypothesis $k\ge1$ ensures $1-2^{-k}>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/Moments.lean#L26-L53

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.natH_mass_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (m : ℕ) :
    ((streamLaw n k).map (fun ω => (firstFailure ω).toNat) {m}).toReal ≤
      ((2 : ℝ)^n/(1-((2 : ℝ)^k)⁻¹))*(1-((2 : ℝ)^k)⁻¹)^m := by sorry
