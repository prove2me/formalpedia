-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_random_fresh_bound
-- name    : OAI.ShortEgyptian.random_fresh_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:04:29.03384+00:00
-- url     : https://prove2.me/theorems/2fc74700-a1ee-419d-8603-cb2c30d5db09
-- title:
--   Products of few factors of size at most $2S^{100}$ stay below $e^{4V/5}$
-- statement:
--   Let $J$ be a finite set, $A$ any set, $p:A\to\mathbb N$ a function, and $S,V$ real numbers with $S\ge2$ and $V>0$. Assume that $p(a)\le2S^{100}$ for every $a\in A$ and that the number of factors satisfies
--   $$|J|\le\frac{3V}{400\log S}.$$
--   Then for every map $f:J\to A$,
--
--   $$
--   \prod_{j\in J}p(f(j))\ <\ e^{4V/5}.
--   $$
--
--   In the random-prime model the primes have size at most $2S^{100}$ and $V=\log u$; the statement then says that a product over a coordinate set of size $s\le3V/(400\log S)$ stays below $u^{4/5}$. This is the size condition that allows bilinear exponential-sum estimates to be applied modulo a large divisor of $u$.
--
--   **Formalization Note** The function $p$ is not required to take prime values here, and $A$ need not be finite. The product is computed in $\mathbb N$ and compared with $e^{4V/5}$ in $\mathbb R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/RandomBounds.lean#L55-L80

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

theorem OAI.ShortEgyptian.random_fresh_bound {J : Type uJ} {A : Type uA} [Fintype J]
    (p : A → ℕ) (S V : ℝ) (hS : 2 ≤ S) (hV : 0 < V)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100)
    (hs : (Fintype.card J:ℝ) ≤ 3*V/(400*Real.log S)) (f : J → A) :
    (∏ j,p (f j):ℕ) < Real.exp (4/5*V) := by sorry
