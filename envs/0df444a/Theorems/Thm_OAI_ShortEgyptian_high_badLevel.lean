-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_high_badLevel
-- name    : OAI.ShortEgyptian.high_badLevel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:25:32.062994+00:00
-- url     : https://prove2.me/theorems/7912e044-5378-4705-ae7e-79413a62e87b
-- title:
--   Few Fourier-bad moduli for dilated subset products of distinct primes
-- statement:
--   Let $J$ be a finite set and let $(p_j)_{j\in J}$ be pairwise distinct primes. For $I\in\{0,1\}^J$ let $t_I=\prod_{j\in J:\,I_j=1}p_j$ be the corresponding subset product, so that $t=(t_I)_{I\in\{0,1\}^J}$ is a family of $2^{|J|}$ natural numbers.
--
--   Write $e(x)=e^{2\pi ix}$. For a multiplier $C\in\mathbb{N}$, a modulus $u\ge1$ and a frequency $l\in\mathbb{N}$ put
--
--   $$\widehat{\mu}_u(l)=\frac{1}{2^{|J|}}\sum_{I\in\{0,1\}^J}e\Big(\frac{lCt_I}{u}\Big).$$
--
--   For $\delta>0$ the modulus $u$ is *Fourier-bad* if $|\widehat{\mu}_u(l)|>\delta^3$ for some integer $l$ with $1\le l\le\lfloor\delta^{-4}\rfloor$. For $X>0$ let $\mathcal{B}(X,\delta)$ be the set of Fourier-bad integers $u$ with $\lfloor X\delta\rfloor+1\le u\le\lfloor X\rfloor$ (the integers in $(X\delta,X]$).
--
--   Fix the absolute constants $D_X=204206$ and $D_C=4D_X=816824$, and for $r\in\mathbb{N}$ let $P(r)=2^r(2r+4)$ and $K(r)=(18\cdot3^{r+3})^4\,((r+2)!)^2\,2^{2r}$. For a real number $S$ put $m=\lfloor S/\log S\rfloor$ and $\rho=e^{-m/10000}$.
--
--   **Theorem.** Let $S,X$ be real numbers and $C$ a natural number, and assume
--
--   - $|J|=m$ and $p_j\le2S^{100}$ for every $j\in J$;
--   - $S\ge2$, $\log S\ge1$ and $m\ge100$;
--   - $P(3D_C)\le\log S$ and $K(3D_C)\,32^{P(3D_C)}\le e^{S/4}$;
--   - $e^S\le X\le e^{D_XS}$ and $e^{D_CS}\le C\le e^{2D_CS}$.
--
--   Then, with $\delta=\rho$,
--
--   $$|\mathcal{B}(X,\rho)|\le X\,e^{-m/1000}.$$
--
--   In words: for all but at most $Xe^{-m/1000}$ integers $u\in(\rho X,X]$, the dilated subset products $Ct_I$ are equidistributed modulo $u$ at all frequencies $1\le l\le\lfloor\rho^{-4}\rfloor$, up to the error $\rho^3$. In the construction of short Egyptian fraction expansions this is the bound on the exceptional moduli at the high levels $X>e^S$, where the divisors used are the subset products of $m$ fixed primes of size about $S^{100}$, dilated by a large multiplier $C$.
--
--   **Formalization Note** $D_X$ and $D_C$ are `dimX` and `dimC`, $m$ is `scaleM S`, $\rho$ is `scaleRho S`, and $P,K$ are `reciprocalPower`, `reciprocalConstantNat`. The family $t$ is `deterministicProduct p`, indexed by `J → Bool`, so the normalisation in $\widehat{\mu}_u(l)$ is the cardinality $2^{|J|}$ of that index type; $\mathcal{B}(X,\rho)$ is `badLevel (deterministicProduct p) C X (scaleRho S)`. Distinctness of the primes is the hypothesis that `p : J → ℕ` is injective with prime values. Floors are natural-number floors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ResidueAssembly.lean#L14-L61

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

open OAI OAI.ShortEgyptian
universe uJ uA uR
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical Filter Topology

theorem OAI.ShortEgyptian.high_badLevel {J : Type uJ} [Fintype J]
    (S X : ℝ) (C : ℕ) (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (hcard : Fintype.card J = scaleM S) (hmax : ∀ j, (p j:ℝ) ≤ 2*S^100)
    (hS : 2 ≤ S) (hlog : 1 ≤ Real.log S) (hm100 : 100 ≤ (scaleM S:ℝ))
    (hP : (reciprocalPower (3*dimC):ℝ) ≤ Real.log S)
    (hconst : (reciprocalConstantNat (3*dimC):ℝ)*32^reciprocalPower (3*dimC) ≤ Real.exp (S/4))
    (hX : Real.exp S ≤ X) (hXD : X ≤ Real.exp ((dimX:ℝ)*S))
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) :
    ((badLevel (deterministicProduct p) C X (scaleRho S)).card:ℝ) ≤
      X*Real.exp (-(1/1000:ℝ)*scaleM S) := by sorry
