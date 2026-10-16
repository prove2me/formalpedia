-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_sample_dvd_auxiliary
-- name    : OAI.ShortEgyptian.sample_dvd_auxiliary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:21:29.963132+00:00
-- url     : https://prove2.me/theorems/0a611ea1-8af6-4ea4-8dd7-b6cb87dae63d
-- title:
--   Every sampled prime product divides the common auxiliary denominator
-- statement:
--   Let $J$ and $R$ be finite sets, $A$ any set, $a\in\mathbb{N}$, $p_0\colon J\to\mathbb{N}$ and $p\colon A\to\mathbb{N}$, and let $(f_k)_{k\in R}$ be a family of maps $f_k\colon J\times\{0,1\}\to A$. Define the *auxiliary denominator*
--
--   $$M=2^{a}\,\prod_{j\in J}p_0(j)\;\prod_{k\in R}\prod_{j\in J}p\bigl(f_k(j,0)\bigr)\,p\bigl(f_k(j,1)\bigr),$$
--
--   and for $k\in R$ and $I\in\{0,1\}^J$ the *sampled product* $t_{f_k}(I)=\prod_{j\in J}p\bigl(f_k(j,I_j)\bigr)$. Then for every $i\in R$ and every $I\in\{0,1\}^J$
--
--   $$
--   t_{f_i}(I)\ \text{ divides }\ M .
--   $$
--
--   No primality, positivity or injectivity is assumed. The lemma shows that every entry of every sampled list is a divisor of one fixed integer $M$, which also contains the factor $2^a$ and the deterministic primes $p_0(j)$. The lists are used in exactly this way, as supplies of divisors of a common denominator.
--
--   **Formalization Note** $M$ is `auxiliaryDenominator a p₀ p f`, $t_{f_i}(I)$ is `sampleProduct p I (f i)`, and $\{0,1\}$ is `Bool` with $0$ = `false` and $1$ = `true`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ListConstruction.lean#L67-L80

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

open OAI OAI.ShortEgyptian
universe uJ uA uR
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.sample_dvd_auxiliary {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A) (i : R) (I : J → Bool) :
    sampleProduct p I (f i) ∣ auxiliaryDenominator a p₀ p f := by sorry
