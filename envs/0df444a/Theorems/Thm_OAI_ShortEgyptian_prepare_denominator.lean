-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_prepare_denominator
-- name    : OAI.ShortEgyptian.prepare_denominator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:51:39.902646+00:00
-- url     : https://prove2.me/theorems/70c099e0-8365-4c3c-9d16-12e8898e1568
-- title:
--   Greedy steps reduce $a/b$ to a remainder whose denominator lies in $[T,T^2)$
-- statement:
--   For a finite list $(n_1,\dots,n_\ell)$ of natural numbers write $\sigma(n_1,\dots,n_\ell)=\sum_{i=1}^{\ell}1/n_i\in\mathbb{Q}$ (the empty list has sum $0$). For natural numbers $a,b$, a real number $T$ and $k\in\mathbb{N}$, call $a/b$ **$(T,k)$-prepared** if there are a list $(n_1,\dots,n_\ell)$ of natural numbers (in any order, repetitions allowed) and natural numbers $A,C$ such that
--
--   1. $n_i\ge 2$ for every $i$, and $\ell\le k$;
--   2. $A\le a$ and $A<C$;
--   3. $\dfrac ab=\sigma(n_1,\dots,n_\ell)+\dfrac AC$ in $\mathbb{Q}$;
--   4. either $A=0$, or $T\le C<T^2$.
--
--   **Theorem.** Let $a,b$ be natural numbers with $0<a<b$, let $T$ be a real number with $T>1$ and $b<T$, and let $k\in\mathbb{N}$ satisfy $T\le\exp(2^k\log 2)=2^{2^k}$. Then $a/b$ is $(T,k+1)$-prepared; that is, there are integers $n_1,\dots,n_\ell\ge 2$ and $A,C\in\mathbb{N}$ with
--
--   $$
--   \frac ab=\frac1{n_1}+\cdots+\frac1{n_\ell}+\frac AC,\qquad \ell\le k+1,\quad A\le a,\quad A<C,\quad \bigl(A=0\ \text{ or }\ T\le C<T^2\bigr).
--   $$
--
--   This is the first phase of an upper bound for the length of short Egyptian fraction expansions: at most $k+1$ greedy unit fractions, with $k$ of order $\log\log T$, are split off from $a/b$ until either nothing remains or the remainder $A/C$ has numerator at most $a$ and denominator in the prescribed window $[T,T^2)$, where a different method takes over.
--
--   **Formalization Note** The predicate is `OAI.ShortEgyptian.Prepared a b T k`, with the reciprocal sum computed in $\mathbb{Q}$ by `unitSum`. The cap $2^{2^k}$ is written as `Real.exp (2^k * Real.log 2)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean#L130-L149

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation

open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq

theorem OAI.ShortEgyptian.prepare_denominator (a b : ℕ) (ha : 0<a) (hab : a<b) (T : ℝ)
    (hT : 1<T) (hbT : (b:ℝ)<T) (k : ℕ)
    (hcap : T ≤ Real.exp ((2:ℝ)^k*Real.log 2)) : Prepared a b T (k+1) := by sorry
