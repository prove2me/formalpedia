-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_levelBad_residue
-- name    : OAI.ShortEgyptian.levelBad_residue
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:40:54.697833+00:00
-- url     : https://prove2.me/theorems/7f36a2ee-1653-4341-9827-34f2781bfd7a
-- title:
--   Small residues of bad numerators are bad at the next level
-- statement:
--   Fix the constants $d_M=2002\cdot102=204204$, $d_X=d_M+2$ and $d_C=4d_X$. For a real number $S$ let $m(S)=\lfloor S/\log S\rfloor$ (a natural number), define the levels $L_j(S)=\exp\big(d_XS-m(S)\,j/10000\big)$ for $j\in\mathbb N$ (non-increasing in $j$), let $\operatorname{depth}(S)=\big\lceil (d_XS-m(S))/(m(S)/10000)\big\rceil$ (a natural number), and for a natural number $C$ let the level multiplier be $Q_j(S,C)=C$ if $e^S<L_j(S)$ and $Q_j(S,C)=1$ otherwise. For positive integers $v,u$ write $r(v,u)=u\lceil v/u\rceil-v$, the least $r\ge0$ with $u\mid v+r$.
--
--   A *unit-sum expansion* of a rational number $x$ is a finite list $(n_1,\dots,n_l)$ of natural numbers with every $n_i\ge2$ and $\sum_i1/n_i=x$ (repetitions allowed). For natural numbers $M,C,K,j$ the set of *bad numerators at level $j$*, written $\mathcal B_j=\mathcal B_j(S,M,C,K)$, consists of the natural numbers $u$ with $1\le u\le\lfloor L_j(S)\rfloor$ such that $u/(M\,Q_j(S,C))$ has no unit-sum expansion of length at most $K+(\operatorname{depth}(S)-j)$, where the subtraction is truncated at $0$.
--
--   Let $S$ be real and let $C,M,K,j,u,t$ be natural numbers with $M>0$, $C>0$, $j<\operatorname{depth}(S)$, $t>0$ and $t\mid M$, and write $Q_j=Q_j(S,C)$. Suppose that $u<M\,Q_j$, that $u\in\mathcal B_j(S,M,C,K)$, and that the residue $v=r(Q_jt,\,u)$ satisfies $v\le L_{j+1}(S)$. Then
--
--   $$
--   r(Q_jt,\,u)\in\mathcal B_{j+1}(S,M,C,K).
--   $$
--
--   So if $u/(MQ_j)$ has no short expansion, then the residue fraction $v/(MQ_{j+1})$ has no expansion with one term fewer allowed, provided $v$ is small enough to be counted at the next level. This lets bad numerators at level $j$ be charged to bad numerators at level $j+1$.
--
--   **Formalization Note** $\mathcal B_j(S,M,C,K)$ is `levelBad S M C K j`; having a unit-sum expansion of $u/(MQ)$ of length at most $k$ is `HasUnitSum M Q u k`, built on `IsUnitSum`. $r(v,u)$ is `residue v u (quotient v u)`, where `quotient v u` is the natural-number ceiling of $v/u$. $L_j(S)$, $Q_j(S,C)$ and $\operatorname{depth}(S)$ are `level S j`, `levelMultiplier S C j` and `depth S`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DescentSets.lean#L104-L120

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

open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.levelBad_residue (S : ℝ) (C M K j u t : ℕ) (hM : 0 < M) (hC : 0 < C)
    (hj : j < depth S) (huM : u < M*levelMultiplier S C j)
    (hu : u ∈ levelBad S M C K j) (ht : 0 < t) (htM : t ∣ M)
    (hy : (residue (levelMultiplier S C j*t) u (quotient (levelMultiplier S C j*t) u):ℝ) ≤ level S (j+1)) :
    residue (levelMultiplier S C j*t) u (quotient (levelMultiplier S C j*t) u) ∈ levelBad S M C K (j+1) := by sorry
