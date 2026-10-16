-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_assemble_residueSystem
-- name    : OAI.ShortEgyptian.assemble_residueSystem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:30:31.086998+00:00
-- url     : https://prove2.me/theorems/45370d46-c39b-479d-b1ae-fafec4610b10
-- title:
--   Assembling a residue system from fixed primes and good sampled prime lists
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
--   Write $e(x)=e^{2\pi ix}$. For a family $s=(s_I)_{I\in\{0,1\}^m}$ of natural numbers, a multiplier $Q\in\mathbb{N}$, a modulus $u\ge1$ and $\delta>0$, the family $s$ is *Fourier-bad* at $(Q,u,\delta)$ if there is an integer $l$ with $1\le l\le\lfloor\delta^{-4}\rfloor$ and
--
--   $$\Big|\frac{1}{2^m}\sum_{I\in\{0,1\}^m}e\Big(\frac{lQs_I}{u}\Big)\Big|>\delta^3 .$$
--
--   Let $\mathcal{B}(s,Q,X,\delta)$ be the set of $u\in\mathcal{U}(X,\delta)$ at which $s$ is Fourier-bad at $(Q,u,\delta)$.
--
--   **Theorem.** Let $S$ be an admissible scale, write $m=m(S)$, and let $C\in\mathbb{N}$ with $e^{D_CS}\le C\le e^{2D_CS}$. Let $p_0:\{0,\dots,m-1\}\to\mathbb{N}$ be injective, with every $p_0(j)$ prime and $S^{100}\le p_0(j)\le2S^{100}$. Let $A$ be a set and $p:A\to\mathbb{N}$ a map whose values are primes with $p(x)\le2S^{100}$. Let $f_0,\dots,f_{999}:\{0,\dots,m-1\}\times\{0,1\}\to A$, and for $I\in\{0,1\}^m$ put $s_i(I)=\prod_{k=0}^{m-1}p\big(f_i(k,I_k)\big)$. Assume:
--
--   (a) for every $j<\operatorname{depth}(S)$ with $X_j\le e^S$,
--
--   $$|\mathcal{B}(s_0,1,X_j,\rho(S))|\le X_j\,e^{-m/1000};$$
--
--   (b) for every integer $u$ with $\lfloor S^{100000}\rfloor+1\le u\le\lfloor e^m\rfloor$ there is $i\in\{0,\dots,999\}$ such that $s_i$ is not Fourier-bad at $(1,u,\delta_u)$, where $\delta_u=e^{-(\log u)/10000}=u^{-1/10000}$.
--
--   Then there exists a residue system for $(S,C)$.
--
--   The theorem reduces the existence of residue systems to two properties of the sampled lists $s_i$ of prime products: a bound on the exceptional moduli at the low levels $X_j\le e^S$, and the existence of a good list at every terminal modulus. The high levels $X_j>e^S$ are handled by the subset products of the fixed primes $p_0(j)$. Both (a) and (b) are supplied by a probabilistic choice of the maps $f_i$.
--
--   **Formalization Note** A residue system is the Lean structure `ResidueSystem S C`; it carries data, so existence is stated as `Nonempty (ResidueSystem S C)`. Admissibility is the structure `ListScale S`; $m(S)$, $\rho(S)$, $X_j$, $Q_j$, $a(S)$, $\operatorname{depth}(S)$, $D_M$, $D_X$, $D_C$, $P$, $K$ are `scaleM`, `scaleRho`, `level`, `levelMultiplier`, `binaryExponent`, `depth`, `dimM`, `dimX`, `dimC`, `reciprocalPower`, `reciprocalConstantNat`; $\{0,\dots,m-1\}$ is `Fin (scaleM S)` and $\{0,1\}$ is `Bool`. The residue $r(v,u)$ is `residue v u (quotient v u)`, where `quotient v u` is the natural-number ceiling of $v/u$, and $\mathcal{U}(X,\delta)$ is `scaleInterval X δ`. Floors and ceilings are natural-number valued. The family $s_i$ is `fun I => sampleProduct p I (f i)`, the sets $\mathcal{B}$ are `badLevel`, and Fourier-badness is `FourierBad`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ResidueSystem.lean#L48-L135

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

theorem OAI.ShortEgyptian.assemble_residueSystem {A : Type uA} (S : ℝ) (h : ListScale S) (C : ℕ)
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S))
    (p₀ : Fin (scaleM S) → ℕ) (hp₀ : ∀ j, (p₀ j).Prime) (hinj : Function.Injective p₀)
    (hp₀max : ∀ j, (p₀ j:ℝ) ≤ 2*S^100) (hp₀min : ∀ j, S^100 ≤ (p₀ j:ℝ))
    (p : A → ℕ) (hp : ∀ x, (p x).Prime) (hpmax : ∀ x, (p x:ℝ) ≤ 2*S^100)
    (f : Fin 1000 → (Fin (scaleM S) × Bool) → A)
    (hf : ∀ j, j < depth S → level S j ≤ Real.exp S →
      ((badLevel (fun I => sampleProduct p I (f 0)) 1 (level S j) (scaleRho S)).card:ℝ) ≤
        level S j*Real.exp (-(1/1000:ℝ)*scaleM S))
    (hterm : ∀ u ∈ Icc (⌊S^100000⌋₊+1) ⌊Real.exp (scaleM S:ℝ)⌋₊,
      ∃ i, ¬FourierBad (fun I => sampleProduct p I (f i)) 1 u
        (Real.exp (-(1/10000:ℝ)*Real.log u))) :
    Nonempty (ResidueSystem S C) := by sorry
