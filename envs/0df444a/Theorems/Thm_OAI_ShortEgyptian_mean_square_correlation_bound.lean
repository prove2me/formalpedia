-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_mean_square_correlation_bound
-- name    : OAI.ShortEgyptian.mean_square_correlation_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:58:57.060602+00:00
-- url     : https://prove2.me/theorems/0bd83604-69ac-427c-987a-e5bffa03e7ea
-- title:
--   Mean-square bound for averages over the Boolean cube of nearly orthogonal functions
-- statement:
--   Let $A$ and $J$ be finite sets with $A\neq\emptyset$, and identify maps $I:J\to\{0,1\}$ with points of the Boolean cube $\{0,1\}^J$. The Hamming distance of $I,K\in\{0,1\}^J$ is $d(I,K)=|\{j\in J: I(j)\neq K(j)\}|$. Let $(F_I)_{I\in\{0,1\}^J}$ be a family of functions $F_I:A\to\mathbb C$ with $|F_I(a)|\le1$ for all $I$ and $a$. Let $k\in\mathbb N$ and $\varepsilon\ge0$, and assume that members indexed by points at Hamming distance at least $k$ are nearly orthogonal:
--   $$\Bigl|\mathbb E_{a\in A}F_I(a)\,\overline{F_K(a)}\Bigr|\le\varepsilon\qquad\text{whenever } d(I,K)\ge k .$$
--   Then, with all averages uniform,
--
--   $$
--   \mathbb E_{a\in A}\Bigl|\mathbb E_{I\in\{0,1\}^J}F_I(a)\Bigr|^{2}\ \le\ 2^{k}\Bigl(\frac34\Bigr)^{|J|}+\varepsilon .
--   $$
--
--   This is a second-moment estimate: an average over the cube of bounded functions is small in mean square as soon as functions indexed by far-apart points are nearly orthogonal. The near-diagonal pairs cost at most the Hamming-ball probability $\Pr_K[d(I,K)<k]\le2^k(3/4)^{|J|}$. It is applied to the exponential phases of random subset products of primes, with $\varepsilon$ supplied by a pair-correlation bound.
--
--   **Formalization Note** The family is a function `F : (J → Bool) → A → ℂ`, the Hamming distance is `hammingDistance I K`, and `𝔼` denotes the uniform average over a finite type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/HammingDistance.lean#L83-L115

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

open OAI OAI.ShortEgyptian
universe uJ uA
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.ShortEgyptian.mean_square_correlation_bound {A : Type uA} {J : Type uJ} [Fintype A] [Nonempty A] [Fintype J]
    (F : (J → Bool) → A → ℂ) (hnorm : ∀ I a, ‖F I a‖ ≤ 1)
    (k : ℕ) (epsilon : ℝ) (heps : 0 ≤ epsilon)
    (hcorr : ∀ I K, k ≤ hammingDistance I K →
      ‖𝔼 a, F I a*(starRingEnd ℂ) (F K a)‖ ≤ epsilon) :
    (𝔼 a, ‖𝔼 I : J → Bool, F I a‖^2) ≤
      (2:ℝ)^k*(3/4:ℝ)^Fintype.card J+epsilon := by sorry
