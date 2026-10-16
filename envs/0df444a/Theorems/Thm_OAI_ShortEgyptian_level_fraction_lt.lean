-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_level_fraction_lt
-- name    : OAI.ShortEgyptian.level_fraction_lt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:39:23.230884+00:00
-- url     : https://prove2.me/theorems/081186b4-26d3-4d2b-ab2e-4d0cc893a58e
-- title:
--   Numerators below the level $L_j$ are smaller than $M\,Q_j$
-- statement:
--   Fix the constants $d_M=2002\cdot102=204204$, $d_X=d_M+2$ and $d_C=4d_X$. For a real number $S$ let $m(S)=\lfloor S/\log S\rfloor$ (a natural number), define the levels $L_j(S)=\exp\big(d_XS-m(S)\,j/10000\big)$ for $j\in\mathbb N$ (non-increasing in $j$), let $\operatorname{depth}(S)=\big\lceil (d_XS-m(S))/(m(S)/10000)\big\rceil$ (a natural number), and for a natural number $C$ let the level multiplier be $Q_j(S,C)=C$ if $e^S<L_j(S)$ and $Q_j(S,C)=1$ otherwise.
--
--   Let $S$ be a real number satisfying the largeness conditions $\mathrm{ListScale}(S)$, namely $S\ge2$, $\log S\ge100$, $100001\log S\le S$, $10^6\log S\le m(S)$, $P\le\log S$ and $A_0\,32^{P}\le e^{S/4}$, where $P=2^{r}(2r+4)$ and $A_0=(18\cdot3^{r+3})^4\,\big((r+2)!\big)^2\,2^{2r}$ with $r=3d_C$, and finally $\operatorname{depth}(S)\,e^{-m(S)/250}<\tfrac12$. Let $C,M,j,u$ be natural numbers with $e^S<M$ and $e^{d_CS}\le C$. If $u\le L_j(S)$, then
--
--   $$
--   u<M\,Q_j(S,C).
--   $$
--
--   The descent produces short Egyptian fraction expansions of fractions $u/(M\,Q_j)$ level by level. This lemma guarantees that every numerator up to the current level gives a proper fraction $u/(MQ_j)<1$, which is the size condition needed to lift an expansion of a residue back to an expansion of $u/(MQ_j)$.
--
--   **Formalization Note** $\mathrm{ListScale}(S)$ is the structure `ListScale S`; $m(S)$ is `scaleM S` (a natural-number floor), $L_j(S)$ is `level S j`, $Q_j(S,C)$ is `levelMultiplier S C j`, $\operatorname{depth}(S)$ is `depth S` (a natural-number ceiling), and $d_X,d_C$ are `dimX`, `dimC`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DescentSets.lean#L62-L79

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

theorem OAI.ShortEgyptian.level_fraction_lt (S : ℝ) (h : ListScale S) (C M j u : ℕ)
    (hM : Real.exp S < (M:ℝ)) (hC : Real.exp ((dimC:ℝ)*S) ≤ C)
    (hu : (u:ℝ) ≤ level S j) : u < M*levelMultiplier S C j := by sorry
