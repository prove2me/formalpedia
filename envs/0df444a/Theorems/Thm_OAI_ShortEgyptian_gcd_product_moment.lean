-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_gcd_product_moment
-- name    : OAI.ShortEgyptian.gcd_product_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:57:17.354338+00:00
-- url     : https://prove2.me/theorems/7dcd16fe-13b2-431f-a7fa-989a55a0ebf4
-- title:
--   Fractional moment bound for the gcd of a random product of primes with a fixed integer
-- statement:
--   Let $J$ and $A$ be finite sets with $A\neq\emptyset$, and let $p:A\to\mathbb N$ assign a prime number $p(x)$ to each $x\in A$ (the primes need not be distinct). Fix a natural number $u$ and real numbers $H\ge0$, $h\ge0$, $a\ge0$ such that $p(x)\le H$ for every $x\in A$ and
--   $$\Pr_{x\in A}\bigl[\,p(x)\mid u\,\bigr]\le h,$$
--   where $x$ is uniform on $A$. Let $f:J\to A$ be a uniformly random map, so that the values $f(j)$, $j\in J$, are independent uniform elements of $A$. Then
--
--   $$
--   \mathbb E_{f}\Bigl[\gcd\Bigl(\prod_{j\in J}p(f(j)),\,u\Bigr)^{a}\Bigr]\ \le\ \exp\bigl(|J|\,h\,H^{a}\bigr).
--   $$
--
--   Thus if a single random prime rarely divides $u$, then a product of $|J|$ independent random primes shares, on average, only a small common factor with $u$, measured through a fractional moment of the gcd. Combined with Markov's inequality, this bounds the probability that such a random product has a large gcd with $u$, which is how degenerate configurations are controlled in the correlation estimates for products of random primes.
--
--   **Formalization Note** Averages are uniform averages `𝔼` over finite types; the real powers $t^{a}$ and $H^{a}$ are `Real.rpow`, and the gcd is the natural-number gcd cast to $\mathbb R$. The case $u=0$ is not excluded (then $\gcd(N,0)=N$, and the hypothesis forces $h\ge1$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/PrimeProducts.lean#L146-L184

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

open OAI OAI.ShortEgyptian
universe uJ uA uB uE uK
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.ShortEgyptian.gcd_product_moment {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (u : ℕ)
    (H h a : ℝ) (hH : 0 ≤ H) (ha : 0 ≤ a) (hprob : 0 ≤ h)
    (hmax : ∀ x, (p x:ℝ) ≤ H)
    (hhit : (𝔼 x, if p x ∣ u then (1:ℝ) else 0) ≤ h) :
    (𝔼 f : J → A, (Nat.gcd (∏ j, p (f j)) u : ℝ)^a) ≤
      Real.exp ((Fintype.card J:ℝ)*h*H^a) := by sorry
