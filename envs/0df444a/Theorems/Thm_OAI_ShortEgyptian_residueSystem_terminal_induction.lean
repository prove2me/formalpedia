-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_residueSystem_terminal_induction
-- name    : OAI.ShortEgyptian.residueSystem_terminal_induction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:36:27.691871+00:00
-- url     : https://prove2.me/theorems/008eebb4-92a8-4e45-a112-b9b047a219b7
-- title:
--   Terminal descent: short unit-fraction expansions of $u/M$ for $u\le e^{m(S)}$
-- statement:
--   Fix the absolute constants $D_M=2002\cdot102=204204$, $D_X=D_M+2=204206$ and $D_C=4D_X=816824$, and for $r\in\mathbb{N}$ let $P(r)=2^r(2r+4)$ and $K(r)=(18\cdot3^{r+3})^4\,((r+2)!)^2\,2^{2r}$. For a real number $S$ put $m(S)=\lfloor S/\log S\rfloor$ and
--
--   $$\operatorname{depth}(S)=\Big\lceil\frac{D_XS-m(S)}{m(S)/10000}\Big\rceil .$$
--
--   A real number $S$ is an *admissible scale* if (i) $S\ge2$; (ii) $\log S\ge100$; (iii) $100001\log S\le S$; (iv) $10^6\log S\le m(S)$; (v) $P(3D_C)\le\log S$; (vi) $K(3D_C)\,32^{P(3D_C)}\le e^{S/4}$; (vii) $\operatorname{depth}(S)\,e^{-m(S)/250}<\tfrac12$. All seven conditions hold for every sufficiently large $S$.
--
--   For natural numbers $v$ and $u\ge1$ let $r(v,u)=u\lceil v/u\rceil-v\in\{0,1,\dots,u-1\}$, the distance from $v$ up to the least multiple of $u$ that is at least $v$. With $m=m(S)$, let $\rho(S)=e^{-m/10000}$, let $X_j=\exp\big(D_XS-jm/10000\big)$ for $j\in\mathbb{N}$ be the *levels* (so $X_0=e^{D_XS}$ and $X_{j+1}=\rho(S)X_j$), given $C\in\mathbb{N}$ let $Q_j=C$ if $e^S<X_j$ and $Q_j=1$ otherwise, and let $a(S)=\lceil100000\log S/\log2\rceil$. For $X,\delta>0$ let $\mathcal{U}(X,\delta)$ be the set of integers $u$ with $\lfloor X\delta\rfloor+1\le u\le\lfloor X\rfloor$, i.e. the integers in $(X\delta,X]$.
--
--   A *residue system* for $(S,C)$ consists of
--
--   1. a natural number $M$ with $e^S<M\le e^{D_MS}$ and $2^{a(S)}\mid M$;
--   2. positive divisors $t_j(I)$ of $M$, one for each $j\in\mathbb{N}$ and $I\in\{0,1\}^m$;
--   3. finite sets $B_j\subseteq\mathbb{N}$, $j\in\mathbb{N}$, with $|B_j|\le X_j\,e^{-m/1000}$ for every $j<\operatorname{depth}(S)$;
--
--   subject to
--
--   4. *(good residues)* for every $j<\operatorname{depth}(S)$ and every $u\in\mathcal{U}(X_j,\rho(S))\setminus B_j$, at least $\rho(S)\,2^m/2$ of the $I\in\{0,1\}^m$ satisfy $r\big(Q_j\,t_j(I),u\big)\le X_{j+1}$;
--   5. *(terminal step)* for every natural number $u$ with $S^{100000}<u\le e^{m}$ there is a positive divisor $t$ of $M$ with $r(t,u)\le u^{9999/10000}$.
--
--   **Theorem.** Let $S$ be an admissible scale, $C\in\mathbb{N}$, and let $M$ be the denominator of a residue system for $(S,C)$. Let $k,u\in\mathbb{N}$ satisfy $u\le e^{m(S)}$ and $\log u\le(10000/9999)^k$. Then there are natural numbers $n_1,\dots,n_L$, each at least $2$ (repetitions allowed), with
--
--   $$\frac{u}{M}=\sum_{i=1}^{L}\frac{1}{n_i}\qquad\text{and}\qquad L\le a(S)+1+k .$$
--
--   This is the terminal stage of the construction of short Egyptian fraction expansions. Since $\log u\le m(S)\le S$ whenever $1\le u\le e^{m(S)}$, the choice $k=\lceil\log S/\log(10000/9999)\rceil$ gives $(10000/9999)^k\ge S$, so every fraction $u/M$ with $u\le e^{m(S)}$ has an expansion with at most $a(S)+1+k=O(\log S)$ unit fractions.
--
--   **Formalization Note** The residue system is a term `R : ResidueSystem S C` and $M$ is `R.M`. The conclusion is `∃ ns, IsUnitSum (u/R.M) ns ∧ ns.length ≤ binaryExponent S+1+k`, where `IsUnitSum x ns` means every entry of the list `ns` is at least $2$ and the sum of reciprocals, computed in $\mathbb{Q}$, equals $x$. With Lean's convention $\log 0=0$ the hypothesis on $\log u$ is automatic for $u=0$, whose expansion is the empty list. Admissibility is the structure `ListScale S`; $m(S)$, $\rho(S)$, $X_j$, $Q_j$, $a(S)$, $\operatorname{depth}(S)$, $D_M$, $D_X$, $D_C$, $P$, $K$ are `scaleM`, `scaleRho`, `level`, `levelMultiplier`, `binaryExponent`, `depth`, `dimM`, `dimX`, `dimC`, `reciprocalPower`, `reciprocalConstantNat`; $\{0,\dots,m-1\}$ is `Fin (scaleM S)` and $\{0,1\}$ is `Bool`. The residue $r(v,u)$ is `residue v u (quotient v u)`, where `quotient v u` is the natural-number ceiling of $v/u$, and $\mathcal{U}(X,\delta)$ is `scaleInterval X δ`. Floors and ceilings are natural-number valued.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/TerminalScale.lean#L35-L88

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

open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.residueSystem_terminal_induction (S : ℝ) (h : ListScale S) (C : ℕ) (R : ResidueSystem S C)
    (k u : ℕ) (hucap : (u:ℝ) ≤ Real.exp (scaleM S:ℝ))
    (hulog : Real.log u ≤ (10000/9999:ℝ)^k) :
    ∃ ns, IsUnitSum ((u:ℚ)/R.M) ns ∧ ns.length ≤ binaryExponent S+1+k := by sorry
