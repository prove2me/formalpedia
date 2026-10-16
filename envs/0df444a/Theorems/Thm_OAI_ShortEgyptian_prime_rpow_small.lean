-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_prime_rpow_small
-- name    : OAI.ShortEgyptian.prime_rpow_small
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:40:40.95982+00:00
-- url     : https://prove2.me/theorems/23b3b3aa-8506-4ddd-9acc-6d94f162d7d9
-- title:
--   For a prime $p$ and $\sigma\ge 1/2$: $0<p^{-\sigma}\le 3/4$
-- statement:
--   Let $p$ be a prime number and let $\sigma\ge\frac12$ be a real number. Then
--
--   $$
--   0<p^{-\sigma}\le\frac34 .
--   $$
--
--   This elementary bound places the variable $x=p^{-\sigma}$ of a local Euler factor in the interval $(0,3/4]$, on which the series $\sum_{j\ge0}(j+1)^rx^j$ converges and is bounded by $\exp(C_rx)$. It is therefore what allows Euler products of divisor-type weights $\tau(n)^rn^{-\sigma}$ to be estimated for every exponent $\sigma\ge1/2$.
--
--   **Formalization Note** $p^{-\sigma}$ is the real power `(p : ℝ) ^ (-σ)` (`Real.rpow`) with positive base.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DivisorWeights.lean#L71-L86

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

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.prime_rpow_small {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1/2 ≤ σ) :
    0 < (p:ℝ)^(-σ) ∧ (p:ℝ)^(-σ) ≤ 3/4 := by sorry
