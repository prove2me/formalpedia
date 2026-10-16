-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_uniform_prime_bilinear_two
-- name    : OAI.ShortEgyptian.uniform_prime_bilinear_two
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:00:36.694614+00:00
-- url     : https://prove2.me/theorems/b080278b-6052-482e-a39f-1acbe283b31e
-- title:
--   Bilinear character sum bound for products of random primes modulo $q$
-- statement:
--   Let $J,K,A$ be finite sets with $A\neq\emptyset$ and $|K|=|J|$, and let $p:A\to\mathbb N$ be an injective map whose values are prime numbers. Let $q\ge1$ be an integer and let $e_q(t)=\exp(2\pi i\,t/q)$ be the standard additive character of $\mathbb Z/q\mathbb Z$. For $f:J\to A$ write $P(f)=\prod_{j\in J}p(f(j))$, and define $P(g)$ likewise for $g:K\to A$. Assume that $P(f)<q$ for all $f:J\to A$ and $P(g)<q$ for all $g:K\to A$. Then for every unit $c\in(\mathbb Z/q\mathbb Z)^{\times}$, with $f$ and $g$ uniformly random,
--
--   $$
--   \Bigl|\,\mathbb E_{f:J\to A}\,\mathbb E_{g:K\to A}\;e_q\bigl(c\,P(f)\,P(g)\bigr)\Bigr|\ \le\ \sqrt{q\Bigl(\frac{|J|^{|J|}}{|A|^{|J|}}\Bigr)^{2}}\;=\;\sqrt q\,\frac{|J|^{|J|}}{|A|^{|J|}} .
--   $$
--
--   This is a bilinear exponential-sum estimate: a product of independent random primes from an injectively labelled set takes no single value with probability larger than $|J|^{|J|}/|A|^{|J|}$, and this spreading forces the bilinear phase $c\,P(f)P(g)$ to be nearly equidistributed modulo $q$. It is the Fourier-analytic input for correlation bounds of subset products of random primes.
--
--   **Formalization Note** The character $e_q$ is `ZMod.stdAddChar`, applied to $c$ times the residues of $P(f)$ and $P(g)$ in `ZMod q`; the hypothesis $P(f)<q$ makes the reduction modulo $q$ injective on the values that occur. The right-hand side is written as `Real.sqrt (q * (|J|^|J| / |A|^|J|)^2)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/SamplePartitions.lean#L94-L119

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

open OAI OAI.ShortEgyptian
universe uJ uA uE uM uK
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.ShortEgyptian.uniform_prime_bilinear_two {J : Type uJ} {K : Type uK} {A : Type uA} [Fintype J] [Fintype K] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (q : ℕ) [NeZero q] (hprod : ∀ f : J → A, ∏ j, p (f j) < q)
    (hprodK : ∀ f : K → A, ∏ j, p (f j) < q) (hcard : Fintype.card K = Fintype.card J) (c : (ZMod q)ˣ) :
    ‖𝔼 f : J → A, 𝔼 g : K → A,
      ZMod.stdAddChar ((c:ZMod q)*((∏ j, p (f j) : ℕ):ZMod q)*((∏ j, p (g j) : ℕ):ZMod q))‖ ≤
      Real.sqrt ((q:ℝ)*((Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J)^2) := by sorry
