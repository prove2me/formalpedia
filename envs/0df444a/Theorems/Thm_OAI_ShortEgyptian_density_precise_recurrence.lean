-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_density_precise_recurrence
-- name    : OAI.ShortEgyptian.density_precise_recurrence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:42:19.315997+00:00
-- url     : https://prove2.me/theorems/0003cc0c-703b-44c8-ad2d-128c28a17f29
-- title:
--   One-step recurrence for the density of numerators without short expansions
-- statement:
--   Fix the constants $d_M=2002\cdot102=204204$, $d_X=d_M+2$, $d_C=4d_X$, $D=2d_C+d_M+1$, $R=49009440000$ and $\alpha=1-1/R$. For a real number $S$ write $m=m(S)=\lfloor S/\log S\rfloor$, $\rho=e^{-m/10000}$, $L_j=\exp(d_XS-mj/10000)=e^{d_XS}\rho^{\,j}$ for the levels ($j\in\mathbb N$), $\operatorname{depth}(S)=\lceil (d_XS-m)/(m/10000)\rceil$, $b(S)=\lceil 100000\log S/\log 2\rceil$ and $T(S)=b(S)+1+\lceil \log S/\log(10000/9999)\rceil$. For a natural number $C$ let $Q_j=C$ if $e^S<L_j$ and $Q_j=1$ otherwise. For $X\in\mathbb R$ and $n\ge1$ let $\tau_X(n)$ be the number of divisors $d\le X$ of $n$, and for positive integers $v,u$ let $r(v,u)=u\lceil v/u\rceil-v$ (the least $r\ge0$ with $u\mid v+r$).
--
--   A *unit-sum expansion* of a rational number $x$ is a finite list $(n_1,\dots,n_l)$ of natural numbers with every $n_i\ge2$ and $\sum_{i}1/n_i=x$ (repetitions allowed). For a natural number $M$, the *bad set* $\mathcal B_j$ at level $j$ consists of the natural numbers $u$ with $1\le u\le\lfloor L_j\rfloor$ such that $u/(MQ_j)$ has no unit-sum expansion of length at most $T(S)+(\operatorname{depth}(S)-j)$ (truncated subtraction), and its *density* is $\delta_j=|\mathcal B_j|/L_j$.
--
--   Let $S$ be a real number and $C$ a natural number such that:
--
--   1. $\mathrm{ListScale}(S)$ holds, that is, $S\ge2$, $\log S\ge100$, $100001\log S\le S$, $10^6\log S\le m(S)$, $P\le\log S$ and $A_0\,32^{P}\le e^{S/4}$, where $P=2^{r}(2r+4)$ and $A_0=(18\cdot3^{r+3})^4\,\big((r+2)!\big)^2\,2^{2r}$ with $r=3d_C$, and finally $\operatorname{depth}(S)\,e^{-m(S)/250}<\tfrac12$;
--   2. $\mathrm{MomentScale}(S)$ holds: for all real $v,Y$ and natural $N$ with $S/(2\log S)\le v\le DS$, $e^{v/2}\le Y\le e^{v}$ and $N\le e^{DS}$, one has $\sum_{N<n\le N+\lfloor Y\rfloor}\tau_{e^{v}}(n)^{R}\le Y\,e^{S^{1/4}}$;
--   3. $e^{d_CS}\le C\le e^{2d_CS}$;
--   4. $\mathcal R$ is a *residue system* for $(S,C)$. This consists of a natural number $M$ (the modulus) with $e^S<M\le e^{d_MS}$ and $2^{b(S)}\mid M$, positive divisors $t_j(i)$ of $M$ indexed by $j\in\mathbb N$ and Boolean vectors $i\in\{0,1\}^m$, and finite sets $E_j\subseteq\mathbb N$, such that for every $j<\operatorname{depth}(S)$ one has $|E_j|\le L_j\,e^{-m/1000}$ and every $u\notin E_j$ with $\lfloor\rho L_j\rfloor<u\le\lfloor L_j\rfloor$ satisfies $\#\{i\in\{0,1\}^m: r(Q_jt_j(i),u)\le L_{j+1}\}\ge\rho\,2^m/2$; moreover every natural number $u$ with $S^{100000}<u\le e^{m}$ admits some $t>0$ with $t\mid M$ and $r(t,u)\le u^{9999/10000}$.
--
--   The bad sets and densities below are formed with the modulus $M$ of $\mathcal R$. Then for every natural number $j<\operatorname{depth}(S)$
--
--   $$
--   \delta_j\le e^{-m/1000}+\rho\,\delta_{j+1}+2\,e^{S^{1/4}/R}\,\delta_{j+1}^{\,\alpha}.
--   $$
--
--   This one-step recurrence bounds the proportion of numerators at level $j$ without a short expansion in terms of the same proportion one level down. The first term pays for the exceptional sets $E_j$, the second for bad numerators that already lie below the next level, and the third, obtained from divisor moments, for numerators whose residues fall into the next bad set. Iterated backwards from the last level, it shows that the top-level bad density is small.
--
--   **Formalization Note** $\mathrm{ListScale}(S)$ and $\mathrm{MomentScale}(S)$ are `ListScale S` and `MomentScale S`; $\mathcal R$ is a term of the structure `ResidueSystem S C` (data, not a proposition) with modulus `R.M`, divisors `R.t j i` and exceptional sets `R.bad j`. The density $\delta_j$ is `levelDensity S R.M C j`, built on `levelBad S R.M C (terminalLength S) j`; $\{0,1\}^m$ is the type `Fin (scaleM S) → Bool`; $R$, $\alpha$, $D$, $T(S)$, $b(S)$ are `descentR`, `descentAlpha`, `momentDimension`, `terminalLength S`, `binaryExponent S`; $r(v,u)$ is `residue v u (quotient v u)` with `quotient v u` the natural-number ceiling of $v/u$. Powers with real exponents are `Real.rpow`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/MomentRecurrence.lean#L106-L143

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

open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical Filter

theorem OAI.ShortEgyptian.density_precise_recurrence (S : ℝ) (h : ListScale S) (hm : MomentScale S) (C : ℕ) (R : ResidueSystem S C)
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S))
    (j : ℕ) (hj : j < depth S) :
    levelDensity S R.M C j ≤ Real.exp (-(1/1000:ℝ)*scaleM S)+
      scaleRho S*levelDensity S R.M C (j+1)+
      2*Real.exp (S^(1/4:ℝ)/(descentR:ℝ))*(levelDensity S R.M C (j+1))^descentAlpha := by sorry
