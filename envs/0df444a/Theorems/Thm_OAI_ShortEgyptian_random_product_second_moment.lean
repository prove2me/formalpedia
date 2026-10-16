-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_random_product_second_moment
-- name    : OAI.ShortEgyptian.random_product_second_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:09:51.881477+00:00
-- url     : https://prove2.me/theorems/ee4a5d29-c58f-40ce-9619-30aece3dcbfc
-- title:
--   Exponentially small second moment of subset-product exponential sums over random primes
-- statement:
--   Let $J$ and $A$ be finite sets with $A\neq\emptyset$, and let $S$ be a real number with $\log S\ge1$, $200\log S\le S$ and
--   $$|J|=m:=\Bigl\lfloor\frac{S}{\log S}\Bigr\rfloor .$$
--   Let $p:A\to\mathbb N$ be an injective map whose values are primes with $p(a)\le2S^{100}$ for all $a$, and assume $|A|\ge S^{99}$. Let $u$ and $l$ be positive integers with $100000\log S\le\log u\le S$ and $l\le\exp\bigl(\frac1{200}\min(m,\log u)\bigr)$. A *sample* is a map $f:J\times\{0,1\}\to A$; under the uniform average its $2|J|$ values are independent uniform elements of $A$. For $I\in\{0,1\}^J$ the corresponding subset product is
--   $$\Pi_I(f)=\prod_{j\in J}p\bigl(f(j,I(j))\bigr),$$
--   that is, at each $j$ one of the two primes $p(f(j,0))$, $p(f(j,1))$ is selected according to $I(j)$. For an integer $u\ge1$ let $e_u(n)=\exp(2\pi i\,n/u)$. Then, with $f$ uniform and $I$ uniform on $\{0,1\}^J$,
--
--   $$
--   \mathbb E_{f}\,\Bigl|\,\mathbb E_{I\in\{0,1\}^J}\,e_u\bigl(l\,\Pi_I(f)\bigr)\Bigr|^{2}\ \le\ \exp\Bigl(-\frac1{100}\min(m,\log u)\Bigr).
--   $$
--
--   For a fixed sample, the numbers $\Pi_I(f)$, $I\in\{0,1\}^J$, are the $2^m$ products obtained by choosing one prime from each of the $m$ random pairs $\{p(f(j,0)),p(f(j,1))\}$, and the inner average is the Fourier coefficient at frequency $l$ of their distribution modulo $u$. The theorem says that, on average over the random primes, these Fourier coefficients are exponentially small for all frequencies $1\le l\le e^{\min(m,\log u)/200}$, so the subset products are well distributed modulo $u$. Through Markov's inequality it bounds the probability that a random choice of primes is Fourier-biased modulo $u$; this is used to select prime lists whose subset products equidistribute modulo $u$ when constructing short Egyptian fraction expansions. The hypotheses on $p$ are met, for instance, by the primes in $(\lfloor S^{100}\rfloor,2\lfloor S^{100}\rfloor]$ once $4000\log S\le S$.
--
--   **Formalization Note** The sample space is `(J × Bool) → A`, $\Pi_I(f)$ is `sampleProduct p I f`, $e_u$ is `ZMod.stdAddChar` on `ZMod u` applied to the residue of $l\,\Pi_I(f)$, $m$ appears as `⌊S/Real.log S⌋₊`, and `𝔼` is the uniform average over a finite type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/RandomMoments.lean#L13-L73

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

open OAI OAI.ShortEgyptian
universe uJ uA
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.ShortEgyptian.random_product_second_moment {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (S : ℝ) (hcard : Fintype.card J = ⌊S/Real.log S⌋₊) (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (u l : ℕ) [NeZero u] (hu : 0 < u) (hl : 0 < l)
    (hV : 100000*Real.log S ≤ Real.log u) (hVS : Real.log u ≤ S)
    (hlmax : (l:ℝ) ≤ Real.exp ((1/200:ℝ)*min (⌊S/Real.log S⌋₊:ℝ) (Real.log u))) :
    (𝔼 f : (J × Bool) → A,
      ‖𝔼 I : J → Bool,
        ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)‖^2) ≤
        Real.exp (-(1/100:ℝ)*min (⌊S/Real.log S⌋₊:ℝ) (Real.log u)) := by sorry
