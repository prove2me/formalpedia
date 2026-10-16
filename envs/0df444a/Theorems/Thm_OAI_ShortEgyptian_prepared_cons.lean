-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_prepared_cons
-- name    : OAI.ShortEgyptian.prepared_cons
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:49:41.303737+00:00
-- url     : https://prove2.me/theorems/35b5f7b4-c79d-45fe-86cb-eed75b821681
-- title:
--   A greedy step extends a prepared decomposition by one unit fraction
-- statement:
--   For natural numbers $a,b,k$ and a real number $T$, call the pair $(a,b)$ *$(T,k)$-prepared* if there are a list $(n_1,\dots,n_l)$ of natural numbers with every $n_i\ge2$ and $l\le k$, and natural numbers $A',C'$ with $A'\le a$ and $A'<C'$, such that $\frac ab=\sum_{i=1}^{l}\frac1{n_i}+\frac{A'}{C'}$ in $\mathbb Q$ and either $A'=0$ or $T\le C'<T^2$. Thus $a/b$ has been split into at most $k$ unit fractions plus a remainder fraction with numerator at most $a$, which either vanishes or has its denominator in the window $[T,T^2)$.
--
--   Let $A,C$ be natural numbers with $0<A<C$, let $T$ be real and $k$ a natural number, and let $z=\lceil C/A\rceil$ and $r=Az-C$ be the greedy denominator and the new numerator, so that $A/C=1/z+r/(Cz)$. Then
--
--   $$
--   (r,\;Cz)\ \text{is }(T,k)\text{-prepared}\quad\Longrightarrow\quad(A,\;C)\ \text{is }(T,k+1)\text{-prepared}.
--   $$
--
--   This is the inductive step of the greedy preparation stage. A decomposition of the greedy remainder $r/(Cz)$ is turned into one of $A/C$ by prepending the unit fraction $1/z$, at the cost of one more term.
--
--   **Formalization Note** Being $(T,k)$-prepared is `Prepared a b T k`; the equation is in $\mathbb Q$, where $a/b$ is read as $0$ if $b=0$. $z$ and $r$ are `quotient C A` and `residue C A (quotient C A)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean#L69-L83

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

theorem OAI.ShortEgyptian.prepared_cons (A C : ℕ) (hA : 0<A) (hAC : A<C) (T : ℝ) (k : ℕ)
    (h : Prepared (residue C A (quotient C A)) (C*quotient C A) T k) :
    Prepared A C T (k+1) := by sorry
