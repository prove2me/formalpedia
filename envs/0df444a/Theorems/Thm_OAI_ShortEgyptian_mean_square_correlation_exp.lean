-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_mean_square_correlation_exp
-- name    : OAI.ShortEgyptian.mean_square_correlation_exp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:02:40.969505+00:00
-- url     : https://prove2.me/theorems/6af17e13-e7bc-4e53-b1df-ae03c93a6eb6
-- title:
--   Mean-square bound over the Boolean cube with error $e^{-|J|/16}+\varepsilon$
-- statement:
--   Let $A$ and $J$ be finite sets with $A\neq\emptyset$, and identify maps $I:J\to\{0,1\}$ with points of the Boolean cube $\{0,1\}^J$. The Hamming distance of $I,K\in\{0,1\}^J$ is $d(I,K)=|\{j\in J: I(j)\neq K(j)\}|$. Let $(F_I)_{I\in\{0,1\}^J}$ be a family of functions $F_I:A\to\mathbb C$ with $|F_I(a)|\le1$ for all $I$ and $a$. Let $k\in\mathbb N$ and $\varepsilon\ge0$, and assume that members indexed by points at Hamming distance at least $k$ are nearly orthogonal:
--   $$\Bigl|\mathbb E_{a\in A}F_I(a)\,\overline{F_K(a)}\Bigr|\le\varepsilon\qquad\text{whenever } d(I,K)\ge k .$$
--   If moreover $4k\le|J|$, then, with all averages uniform,
--
--   $$
--   \mathbb E_{a\in A}\Bigl|\mathbb E_{I\in\{0,1\}^J}F_I(a)\Bigr|^{2}\ \le\ e^{-|J|/16}+\varepsilon .
--   $$
--
--   This is the exponential form of the cube mean-square bound: as long as near-orthogonality holds beyond Hamming distance $k\le|J|/4$, the contribution of nearby pairs decays exponentially in the dimension $|J|$. It is the form used for averages of exponential phases of random subset products of primes.
--
--   **Formalization Note** The family is a function `F : (J → Bool) → A → ℂ`, the Hamming distance is `hammingDistance I K`, and `𝔼` denotes the uniform average over a finite type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ProductCorrelations.lean#L150-L169

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

theorem OAI.ShortEgyptian.mean_square_correlation_exp {A : Type uA} {J : Type uJ} [Fintype A] [Nonempty A] [Fintype J]
    (F : (J → Bool) → A → ℂ) (hnorm : ∀ I a, ‖F I a‖ ≤ 1)
    (k : ℕ) (hk : 4*k ≤ Fintype.card J) (epsilon : ℝ) (heps : 0 ≤ epsilon)
    (hcorr : ∀ I K, k ≤ hammingDistance I K →
      ‖𝔼 a, F I a*(starRingEnd ℂ) (F K a)‖ ≤ epsilon) :
    (𝔼 a, ‖𝔼 I : J → Bool, F I a‖^2) ≤
      Real.exp (-(Fintype.card J:ℝ)/16)+epsilon := by sorry
