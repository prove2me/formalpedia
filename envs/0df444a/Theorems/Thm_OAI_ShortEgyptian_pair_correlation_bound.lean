-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_pair_correlation_bound
-- name    : OAI.ShortEgyptian.pair_correlation_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:01:29.133526+00:00
-- url     : https://prove2.me/theorems/699bff99-ee1a-43fe-906c-4cf35c907ba0
-- title:
--   Correlation bound for the phases of two subset products of random primes
-- statement:
--   Let $J$ and $A$ be finite sets with $A\neq\emptyset$, and let $p:A\to\mathbb N$ be an injective map whose values are prime numbers. A *sample* is a map $f:J\times\{0,1\}\to A$; under the uniform average its $2|J|$ values are independent uniform elements of $A$. For $I\in\{0,1\}^J$ the corresponding subset product is
--   $$\Pi_I(f)=\prod_{j\in J}p\bigl(f(j,I(j))\bigr),$$
--   that is, at each $j$ one of the two primes $p(f(j,0))$, $p(f(j,1))$ is selected according to $I(j)$. For an integer $u\ge1$ let $e_u(n)=\exp(2\pi i\,n/u)$.
--
--   Fix integers $u\ge1$ and $l\ge1$, vectors $I,K\in\{0,1\}^J$, and disjoint sets $L,R\subseteq J$ with $|L|=|R|$ such that $I(j)\neq K(j)$ for every $j\in L\cup R$; put $C=J\setminus(L\cup R)$. Let $Q,G,B,M,a$ be real numbers with $G>0$, $B\ge0$, $a\ge0$, and assume:
--
--   1. $l\,G\,Q\le u$;
--   2. $\prod_{j\in L}p(x(j))<Q$ for every $x:L\to A$, and $\prod_{j\in R}p(y(j))<Q$ for every $y:R\to A$;
--   3. $|L|^{|L|}/|A|^{|L|}\le B$;
--   4. $\mathbb E_{z:C\to A}\,\gcd\bigl(\prod_{j\in C}p(z(j)),\,u\bigr)^{a}\le M$, with $z$ uniform.
--
--   Then
--
--   $$
--   \Bigl|\,\mathbb E_{f}\;e_u\bigl(l\,\Pi_I(f)\bigr)\,\overline{e_u\bigl(l\,\Pi_K(f)\bigr)}\Bigr|\ \le\ \frac{M}{G^{a}}+\sqrt u\,B .
--   $$
--
--   The left side is the correlation, over the random sample, between the phases of two subset products whose index vectors differ on $L\cup R$. The bound has a degenerate part $M/G^a$, which controls the probability that the part of the product shared by both index vectors has a gcd at least $G$ with $u$, and a generic part $\sqrt u\,B$ coming from a bilinear exponential-sum estimate over the fresh primes on $L$ and $R$. With suitable parameters it supplies the near-orthogonality hypothesis of the mean-square bound over the Boolean cube.
--
--   **Formalization Note** The sample space is `(J × Bool) → A`, $\Pi_I$ is `sampleProduct p I`, and $e_u$ is `ZMod.stdAddChar` applied to the natural number $l\,\Pi_I(f)$ reduced modulo $u$; the powers $t^a$ and $G^a$ are real powers (`Real.rpow`). The conditions on $L$ and $R$ appear as `Disjoint L R`, `R.card = L.card` and `I j ≠ K j` for all `j ∈ L` and all `j ∈ R`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ProductCorrelations.lean#L68-L138

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

theorem OAI.ShortEgyptian.pair_correlation_bound {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (u l : ℕ) [NeZero u] (hu : 0 < u) (hl : 0 < l) (I K : J → Bool)
    (L R : Finset J) (hdis : Disjoint L R) (hcard : R.card = L.card)
    (hdiffL : ∀ j ∈ L, I j ≠ K j) (hdiffR : ∀ j ∈ R, I j ≠ K j)
    (Q G B M a : ℝ) (hG : 0 < G) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hscale : (l:ℝ)*G*Q ≤ u)
    (hprod : ∀ f : L → A, (∏ j, p (f j):ℕ) < Q)
    (hprodR : ∀ f : R → A, (∏ j, p (f j):ℕ) < Q)
    (hatom : (L.card:ℝ)^L.card/(Fintype.card A:ℝ)^L.card ≤ B)
    (hMoment : (𝔼 z : ((L∪R)ᶜ : Finset J) → A, (Nat.gcd (∏ j,p (z j)) u:ℝ)^a) ≤ M) :
    ‖𝔼 f : (J × Bool) → A,
      ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K f:ℕ):ZMod u))‖ ≤
        M/G^a+Real.sqrt u*B := by sorry
