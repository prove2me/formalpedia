-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_exists_residueSystem
-- name    : OAI.ShortEgyptian.exists_residueSystem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:32:52.940008+00:00
-- url     : https://prove2.me/theorems/566016a6-3640-41f4-99e5-196de7321878
-- title:
--   Existence of a residue system at every admissible scale
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
--   **Theorem.** Let $S$ be an admissible scale and let $C$ be a natural number with
--
--   $$e^{D_CS}\le C\le e^{2D_CS}.$$
--
--   Then there exists a residue system for $(S,C)$.
--
--   Residue systems are the arithmetic input of the upper bound for shortest Egyptian fraction expansions. A residue system provides a single denominator $M$ of size between $e^S$ and $e^{D_MS}$ together with many divisors of $M$ whose residues let one shrink numerators level by level, from the top level $X_0=e^{D_XS}$ down to $e^{m(S)}$ (good residues), and then further to the binary range below $2^{a(S)}$ (terminal step).
--
--   **Formalization Note** A residue system is the Lean structure `ResidueSystem S C`, and the theorem asserts `Nonempty (ResidueSystem S C)`. Admissibility is the structure `ListScale S`; $m(S)$, $\rho(S)$, $X_j$, $Q_j$, $a(S)$, $\operatorname{depth}(S)$, $D_M$, $D_X$, $D_C$, $P$, $K$ are `scaleM`, `scaleRho`, `level`, `levelMultiplier`, `binaryExponent`, `depth`, `dimM`, `dimX`, `dimC`, `reciprocalPower`, `reciprocalConstantNat`; $\{0,\dots,m-1\}$ is `Fin (scaleM S)` and $\{0,1\}$ is `Bool`. The residue $r(v,u)$ is `residue v u (quotient v u)`, where `quotient v u` is the natural-number ceiling of $v/u$, and $\mathcal{U}(X,\delta)$ is `scaleInterval X δ`. Floors and ceilings are natural-number valued.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ResidueSystem.lean#L137-L176

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

open OAI OAI.ShortEgyptian
universe uA
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.exists_residueSystem (S : ℝ) (h : ListScale S) (C : ℕ)
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) :
    Nonempty (ResidueSystem S C) := by sorry
