-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_prepare_aux
-- name    : OAI.ShortEgyptian.prepare_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:50:47.969435+00:00
-- url     : https://prove2.me/theorems/48f6e2f4-9bb3-4c76-9f21-583db366135b
-- title:
--   Greedy preparation: $k$ greedy steps reach a denominator in $[T,T^2)$
-- statement:
--   For natural numbers $a,b,k$ and a real number $T$, call the pair $(a,b)$ *$(T,k)$-prepared* if there are a list $(n_1,\dots,n_l)$ of natural numbers with every $n_i\ge2$ and $l\le k$, and natural numbers $A',C'$ with $A'\le a$ and $A'<C'$, such that $\frac ab=\sum_{i=1}^{l}\frac1{n_i}+\frac{A'}{C'}$ in $\mathbb Q$ and either $A'=0$ or $T\le C'<T^2$. Thus $a/b$ has been split into at most $k$ unit fractions plus a remainder fraction with numerator at most $a$, which either vanishes or has its denominator in the window $[T,T^2)$.
--
--   Let $k,A,C$ be natural numbers with $A<C$, and let $T,v$ be real numbers with $T>1$ and $v>0$. Assume
--
--   $$
--   C<T^2,\qquad\frac AC\le e^{-v},\qquad T\le\exp\big(2^{k}v\big).
--   $$
--
--   Then $(A,C)$ is $(T,k)$-prepared.
--
--   Starting from a fraction that is already at most $e^{-v}$, at most $k$ greedy steps therefore suffice either to finish exactly or to reach a remainder whose denominator lies in the window $[T,T^2)$. Since $2^kv\ge\log T$ is all that is required, the number of greedy steps needed is only about $\log_2(\log T/v)$. This preparation makes the remainder's denominator comparable to a prescribed scale before the main construction is applied.
--
--   **Formalization Note** Being $(T,k)$-prepared is `Prepared A C T k`. The hypothesis $A/C\le e^{-v}$ is stated in $\mathbb R$, and the representation of $A/C$ inside `Prepared` is an equation in $\mathbb Q$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean#L85-L128

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

theorem OAI.ShortEgyptian.prepare_aux (k : ℕ) (A C : ℕ) (hAC : A<C) (T v : ℝ) (hT : 1<T)
    (hv : 0<v) (hsize : (C:ℝ)<T^2) (hsmall : (A:ℝ)/C ≤ Real.exp (-v))
    (hcap : T ≤ Real.exp ((2:ℝ)^k*v)) : Prepared A C T k := by sorry
