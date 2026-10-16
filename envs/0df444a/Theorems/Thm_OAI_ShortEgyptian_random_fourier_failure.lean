-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_random_fourier_failure
-- name    : OAI.ShortEgyptian.random_fourier_failure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:13:39.55791+00:00
-- url     : https://prove2.me/theorems/3077501a-0dfe-4787-9f61-c82bc6326bfd
-- title:
--   A random list of prime products is Fourier-bad modulo $u$ with probability at most $e^{-v/200}$
-- statement:
--   Let $e(x)=\exp(2\pi i x)$. For a finite index set $\mathcal I$, a list $t\colon\mathcal I\to\mathbb{N}$ and natural numbers $u,l$, the *phase average* is
--
--   $$\Phi_t(u,l)=\frac{1}{|\mathcal I|}\sum_{i\in\mathcal I}e\Bigl(\frac{l\,t_i}{u}\Bigr),$$
--
--   and for $\delta>0$ the list is *Fourier-bad at modulus $u$ with parameter $\delta$* if $|\Phi_t(u,l)|>\delta^3$ for some integer $l$ with $1\le l\le\lfloor\delta^{-4}\rfloor$.
--
--   The random lists are built as follows. Let $J$ and $A$ be finite sets with $A$ nonempty, and let $p\colon A\to\mathbb{N}$. A map $f\colon J\times\{0,1\}\to A$ assigns two labels $f(j,0),f(j,1)$ to each $j\in J$, and for $I\in\{0,1\}^J$ we put
--
--   $$t_f(I)=\prod_{j\in J}p\bigl(f(j,I_j)\bigr),$$
--
--   a list of $2^{|J|}$ products indexed by $\{0,1\}^J$. The map $f$ is chosen uniformly at random among all $|A|^{2|J|}$ maps.
--
--   **Theorem.** Let $S,v$ be real numbers and $u$ a natural number, and assume:
--
--   1. $|J|=\lfloor S/\log S\rfloor$, $\log S\ge1$ and $200\log S\le S$;
--   2. $p$ is injective, every $p(a)$ is prime, $p(a)\le 2S^{100}$ for all $a\in A$, and $|A|\ge S^{99}$;
--   3. $u>0$ and $100000\log S\le\log u\le S$;
--   4. $v\ge0$ and $\frac{99}{100}v\le\min\bigl(\lfloor S/\log S\rfloor,\log u\bigr)$.
--
--   Then
--
--   $$
--   \Pr_f\Bigl[\,t_f\text{ is Fourier-bad at modulus }u\text{ with parameter }\delta=e^{-v/10000}\Bigr]\;\le\;e^{-v/200}.
--   $$
--
--   So a random list of $2^{\lfloor S/\log S\rfloor}$ products, in which each coordinate $j$ chooses one of two independent uniformly random primes from $p(A)$, is equidistributed modulo $u$ at all frequencies $l\le e^{v/2500}$, up to error $e^{-3v/10000}$, except with probability exponentially small in $v$. Since $v$ may be as large as about $\min(|J|,\log u)$, the failure probabilities are small enough for union bounds over many moduli.
--
--   **Formalization Note** The probability is the average `𝔼 f : (J × Bool) → A` of an indicator, $\{0,1\}$ is `Bool`, $t_f(I)$ is `sampleProduct p I f`, $\Phi$ is `phaseAverage` with multiplier $Q=1$, and Fourier-badness is `FourierBad (fun I => sampleProduct p I f) 1 u δ`. The floors are natural-number floors `⌊·⌋₊`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ListSelection.lean#L105-L140

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

open OAI OAI.ShortEgyptian
universe uI uΩ uJ uA uE uD uU
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.random_fourier_failure {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (S v : ℝ) (hcard : Fintype.card J = ⌊S/Real.log S⌋₊)
    (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (u : ℕ) (hu : 0 < u) (hV : 100000*Real.log S ≤ Real.log u) (hVS : Real.log u ≤ S)
    (hv : 0 ≤ v) (hvw : (99/100:ℝ)*v ≤ min (⌊S/Real.log S⌋₊:ℝ) (Real.log u)) :
    (𝔼 f : (J × Bool) → A,
      if FourierBad (fun I => sampleProduct p I f) 1 u (Real.exp (-(1/10000:ℝ)*v)) then (1:ℝ) else 0) ≤
        Real.exp (-(1/200:ℝ)*v) := by sorry
