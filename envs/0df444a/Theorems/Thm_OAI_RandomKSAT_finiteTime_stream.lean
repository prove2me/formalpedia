-- Prove2me | Theorems.Thm_OAI_RandomKSAT_finiteTime_stream
-- name    : OAI.RandomKSAT.finiteTime_stream
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:59:42.866519+00:00
-- url     : https://prove2.me/theorems/f4c86e3d-5843-4108-8a5e-f3babcd80fc7
-- title:
--   Counting satisfiable prefixes among the first $L$ clauses gives $\min(\tau,L)$
-- statement:
--   Fix natural numbers $n$ and $k$, and write $[n]=\{0,1,\dots,n-1\}$ for the set of Boolean variables. An *assignment* is a map $a:[n]\to\{\mathrm T,\mathrm F\}$. A *clause of width $k$* is a pair $c=(V,\beta)$ of a set $V\subseteq[n]$ with $|V|=k$ and a sign map $\beta:V\to\{\mathrm T,\mathrm F\}$; the assignment $a$ *satisfies* $c$ if $a(v)=\beta(v)$ for at least one $v\in V$. Let $\mathcal C_{n,k}$ be the finite set of all such clauses; it has $\binom nk2^k$ elements.
--
--   A *stream* is an infinite sequence $\omega=(\omega_0,\omega_1,\omega_2,\dots)$ of clauses from $\mathcal C_{n,k}$. Write $\mathrm{SAT}_m(\omega)$ if some single assignment satisfies all of $\omega_0,\dots,\omega_{m-1}$ (for $m=0$ this always holds). The *first failure time* of $\omega$ is $\tau(\omega)=\min\{m\in\mathbb N:\ \mathrm{SAT}_m(\omega)\text{ fails}\}\in\mathbb N\cup\{\infty\}$, with $\tau(\omega)=\infty$ if every prefix is satisfiable.
--
--   For a finite sequence $\mathbf c=(c_0,\dots,c_{L-1})$ of clauses define
--   $$
--   F_L(\mathbf c)=\#\big\{m\in\{0,\dots,L-1\}:\ c_0,\dots,c_{m-1}\text{ have a common satisfying assignment}\big\}.
--   $$
--
--   **Theorem.** For all $n,k,L\in\mathbb N$ and every stream $\omega$,
--   $$
--   F_L(\omega_0,\dots,\omega_{L-1})=\min\big(\tau(\omega),L\big).
--   $$
--
--   Thus the first failure time truncated at $L$ is an explicit function of the first $L$ clauses alone. With $L=\lfloor Bn\rfloor$ this identifies the capped first failure time with a function on the finite product $\mathcal C_{n,k}^L$, so that variance inequalities for functions of finitely many independent variables become available.
--
--   **Formalization Note** $F_L$ is `finiteTime`, the real sum over `m : Fin L` of the indicator of `finiteSAT cs m` (some assignment satisfies every `cs j` with `j < m`). The right-hand side is `(min (firstFailure ω) L).toNat` cast to $\mathbb R$; the minimum is finite, so no convention about $\infty$ enters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FiniteVariance.lean#L168-L182

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

theorem OAI.RandomKSAT.finiteTime_stream {n k L : ℕ} (ω : Stream n k) :
    finiteTime (fun j : Fin L => ω j) = ((min (firstFailure ω) (L : ℕ∞)).toNat : ℝ) := by sorry
