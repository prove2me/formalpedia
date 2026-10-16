-- Prove2me | Theorems.Thm_OAI_RandomKSAT_lt_firstFailure_iff
-- name    : OAI.RandomKSAT.lt_firstFailure_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:51:51.17139+00:00
-- url     : https://prove2.me/theorems/ce69132e-bc89-4986-aae2-ebf954285471
-- title:
--   The first failure time exceeds $m$ exactly when the first $m$ clauses are satisfiable
-- statement:
--   Fix natural numbers $n$ and $k$, and write $[n]=\{0,1,\dots,n-1\}$ for the set of Boolean variables. An *assignment* is a map $a:[n]\to\{\mathrm T,\mathrm F\}$. A *clause of width $k$* is a pair $c=(V,\beta)$ of a set $V\subseteq[n]$ with $|V|=k$ and a sign map $\beta:V\to\{\mathrm T,\mathrm F\}$; the assignment $a$ *satisfies* $c$ if $a(v)=\beta(v)$ for at least one $v\in V$. Let $\mathcal C_{n,k}$ be the finite set of all such clauses; it has $\binom nk2^k$ elements.
--
--   A *stream* is an infinite sequence $\omega=(\omega_0,\omega_1,\omega_2,\dots)$ of clauses from $\mathcal C_{n,k}$. Write $\mathrm{SAT}_m(\omega)$ if some single assignment satisfies all of $\omega_0,\dots,\omega_{m-1}$ (for $m=0$ this always holds). The *first failure time* of $\omega$ is $\tau(\omega)=\min\{m\in\mathbb N:\ \mathrm{SAT}_m(\omega)\text{ fails}\}\in\mathbb N\cup\{\infty\}$, with $\tau(\omega)=\infty$ if every prefix is satisfiable.
--
--   **Theorem.** For every stream $\omega$ and every $m\in\mathbb N$,
--   $$
--   m<\tau(\omega)\iff\mathrm{SAT}_m(\omega),
--   $$
--   that is, $\tau(\omega)>m$ if and only if some single assignment satisfies $\omega_0,\dots,\omega_{m-1}$.
--
--   This identity translates events about the first failure time into satisfiability events about a finite prefix. For example, $\{\tau>m\}$ is the union, over the $2^n$ assignments $a$, of the events that $a$ satisfies the first $m$ clauses. It is the basic tool for the measurability of $\tau$, for tail bounds on $\tau$, and for identifying truncations of $\tau$ with functions of finitely many clauses.
--
--   **Formalization Note** `firstFailure ω` is an element of `ℕ∞`, defined as the infimum of the image of $\{m:\ \neg\,\mathrm{SAT}_m(\omega)\}$ in $\mathbb N\cup\{\infty\}$; the infimum of the empty set is $\infty$. The comparison $m<\tau(\omega)$ is taken in `ℕ∞`. No assumption on $n$ and $k$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FirstFailure.lean#L21-L35

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.lt_firstFailure_iff {n k : ℕ} (ω : Stream n k) (m : ℕ) :
    (m : ℕ∞) < firstFailure ω ↔ PrefixSAT ω m := by sorry
