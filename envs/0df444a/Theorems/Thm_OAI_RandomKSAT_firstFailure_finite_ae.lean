-- Prove2me | Theorems.Thm_OAI_RandomKSAT_firstFailure_finite_ae
-- name    : OAI.RandomKSAT.firstFailure_finite_ae
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:53:03.955802+00:00
-- url     : https://prove2.me/theorems/233f8bb7-a7c7-49e6-8ec6-0d3b647acfdc
-- title:
--   A stream of independent random clauses almost surely becomes unsatisfiable
-- statement:
--   Fix natural numbers $n$ and $k$, and write $[n]=\{0,1,\dots,n-1\}$ for the set of Boolean variables. An *assignment* is a map $a:[n]\to\{\mathrm T,\mathrm F\}$. A *clause of width $k$* is a pair $c=(V,\beta)$ of a set $V\subseteq[n]$ with $|V|=k$ and a sign map $\beta:V\to\{\mathrm T,\mathrm F\}$; the assignment $a$ *satisfies* $c$ if $a(v)=\beta(v)$ for at least one $v\in V$. Let $\mathcal C_{n,k}$ be the finite set of all such clauses; it has $\binom nk2^k$ elements.
--
--   A *stream* is an infinite sequence $\omega=(\omega_0,\omega_1,\omega_2,\dots)$ of clauses from $\mathcal C_{n,k}$. Write $\mathrm{SAT}_m(\omega)$ if some single assignment satisfies all of $\omega_0,\dots,\omega_{m-1}$ (for $m=0$ this always holds). The *first failure time* of $\omega$ is $\tau(\omega)=\min\{m\in\mathbb N:\ \mathrm{SAT}_m(\omega)\text{ fails}\}\in\mathbb N\cup\{\infty\}$, with $\tau(\omega)=\infty$ if every prefix is satisfiable. Let $\mathbb P_{n,k}$ be the law on streams under which $\omega_0,\omega_1,\dots$ are independent and each is uniformly distributed on $\mathcal C_{n,k}$; it is a probability measure as soon as $k\le n$, so that clauses exist.
--
--   **Theorem.** If $k\le n$, then
--   $$
--   \mathbb P_{n,k}\big(\tau(\omega)<\infty\big)=1,
--   $$
--   i.e. for almost every stream some finite prefix has no common satisfying assignment.
--
--   The real-valued first failure time used in the variance estimates for random $k$-SAT reads the value $\tau=\infty$ as $0$. This theorem shows that this convention only matters on a null set, so that this real-valued time coincides with $\tau$ almost surely.
--
--   **Formalization Note** The statement is `∀ᵐ ω ∂streamLaw n k, firstFailure ω < ⊤`, where `streamLaw n k` is the product measure `Measure.infinitePi` of copies of the uniform measure `clauseLaw n k` on clauses. The hypothesis $k\le n$ guarantees that clauses of width $k$ exist, so that these are probability measures.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FirstFailure.lean#L123-L140

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.firstFailure_finite_ae {n k : ℕ} (hkn : k ≤ n) :
    ∀ᵐ ω ∂streamLaw n k, firstFailure ω < ⊤ := by sorry
