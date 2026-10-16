-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_choose_random_lists
-- name    : OAI.ShortEgyptian.choose_random_lists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:19:59.473794+00:00
-- url     : https://prove2.me/theorems/ce187ee2-1a22-4ee1-9ffd-5639e4f45827
-- title:
--   Choosing 1000 prime-product lists: few Fourier-bad moduli at every scale, and a good list for every terminal modulus
-- statement:
--   **Notation.** Let $e(x)=\exp(2\pi i x)$. For a finite index set $\mathcal I$, a list $t\colon\mathcal I\to\mathbb{N}$, natural numbers $u,l$ and $\delta>0$, write $\Phi_t(u,l)=\frac1{|\mathcal I|}\sum_{i\in\mathcal I}e(l\,t_i/u)$. Call $u$ *Fourier-bad for $t$ at parameter $\delta$* if $|\Phi_t(u,l)|>\delta^3$ for some integer $l$ with $1\le l\le\lfloor\delta^{-4}\rfloor$, and for real $X$ put
--
--   $$\mathcal B_t(X,\delta)=\bigl\{u\in\mathbb{N}:\ \lfloor X\delta\rfloor<u\le\lfloor X\rfloor,\ u\text{ is Fourier-bad for }t\text{ at parameter }\delta\bigr\}.$$
--
--   Let $J,A$ be finite sets with $A$ nonempty and let $p\colon A\to\mathbb{N}$. A map $f\colon J\times\{0,1\}\to A$ defines the list $t_f$ indexed by $I\in\{0,1\}^J$, given by $t_f(I)=\prod_{j\in J}p\bigl(f(j,I_j)\bigr)$.
--
--   **Theorem.** Let $S$ be a real number and $m=\lfloor S/\log S\rfloor$. Let $D$ be a finite set, $X\colon D\to\mathbb{R}$, and $U$ a finite set of natural numbers. Assume:
--
--   1. $|J|=m$, $\log S\ge1$ and $200\log S\le S$;
--   2. $p$ is injective, every $p(a)$ is prime, $p(a)\le2S^{100}$ for all $a\in A$, and $|A|\ge S^{99}$;
--   3. $100000\log S\le\frac{99}{100}m$ and $m\le S$;
--   4. $e^{m}\le X_d\le e^{S}$ for every $d\in D$;
--   5. every $u\in U$ satisfies $u\ge3$ and $100000\log S\le\log u\le m$;
--   6. $|D|\,e^{-m/250}<\frac12$.
--
--   Then there are maps $f_0,f_1,\dots,f_{999}\colon J\times\{0,1\}\to A$ with the following two properties.
--
--   1. **Few bad moduli for the first list.** For every $d\in D$,
--
--      $$
--      \#\,\mathcal B_{t_{f_0}}\bigl(X_d,\,e^{-m/10000}\bigr)\le X_d\,e^{-m/1000}.
--      $$
--
--   2. **Every terminal modulus is good for some list.** For every $u\in U$ there is an index $i\in\{0,\dots,999\}$ such that $u$ is not Fourier-bad for $t_{f_i}$ at parameter $e^{-\log u/10000}=u^{-1/10000}$.
--
--   This theorem supplies the lists of prime products for the construction of short Egyptian fraction expansions. The first list is well distributed modulo all but at most $X_de^{-m/1000}$ of the moduli in each window $(X_de^{-m/10000},X_d]$, one window for each scale $d\in D$. Each of the finitely many terminal moduli in $U$ is handled by at least one of the $1000$ lists.
--
--   **Formalization Note** The lists are `fun I => sampleProduct p I (f i)` with multiplier $Q=1$, $\{0,1\}$ is `Bool`, $\mathcal B$ is `badLevel`, Fourier-badness is `FourierBad`, the indices form `Fin 1000` and $f_0$ is `f 0`. All floors are natural-number floors `⌊·⌋₊`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/LevelSelection.lean#L101-L153

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

open OAI OAI.ShortEgyptian
universe uI uΩ uJ uA uD
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.choose_random_lists {J : Type uJ} {A : Type uA} {D : Type uD} [Fintype J] [Fintype A] [Nonempty A] [Fintype D]
    (S : ℝ) (hcard : Fintype.card J = ⌊S/Real.log S⌋₊)
    (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (hm : 100000*Real.log S ≤ (99/100:ℝ)*(⌊S/Real.log S⌋₊:ℝ))
    (hmS : (⌊S/Real.log S⌋₊:ℝ) ≤ S)
    (X : D → ℝ) (hX : ∀ d, Real.exp (⌊S/Real.log S⌋₊:ℝ) ≤ X d ∧ X d ≤ Real.exp S)
    (U : Finset ℕ) (hU : ∀ u ∈ U, 3 ≤ u ∧ 100000*Real.log S ≤ Real.log u ∧ Real.log u ≤ (⌊S/Real.log S⌋₊:ℝ))
    (hsmall : (Fintype.card D:ℝ)*Real.exp (-(1/250:ℝ)*(⌊S/Real.log S⌋₊:ℝ)) < 1/2) :
    ∃ f : Fin 1000 → (J × Bool) → A,
      (∀ d, ((badLevel (fun I => sampleProduct p I (f 0)) 1 (X d)
        (Real.exp (-(1/10000:ℝ)*(⌊S/Real.log S⌋₊:ℝ)))).card:ℝ) ≤
          X d*Real.exp (-(1/1000:ℝ)*(⌊S/Real.log S⌋₊:ℝ))) ∧
      (∀ u ∈ U, ∃ i, ¬FourierBad (fun I => sampleProduct p I (f i)) 1 u
        (Real.exp (-(1/10000:ℝ)*Real.log u))) := by sorry
