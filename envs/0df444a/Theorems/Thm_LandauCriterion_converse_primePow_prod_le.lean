-- Prove2me | Theorems.Thm_LandauCriterion_converse_primePow_prod_le
-- name    : LandauCriterion.converse_primePow_prod_le
-- status  : Open
-- author  : @pitimespi
-- created : 2026-11-01T18:53:14.628797+00:00
-- url     : https://prove2.me/theorems/4343cdc5-33df-4176-a16c-6a194366ab85
-- title:
--   Converse knapsack bound for Landau's function
-- statement:
--   Let $t$ be a finite set of prime powers with distinct primes: there is a function assigning to each $q \in t$ a prime $f(q)$ with $q = f(q)^k$ for some $k \ge 1$, and $f$ is injective on $t$. If the elements of $t$ sum to at most $n$, then their product is at most $g(n)$ (here in the form `landauLocal n`, the platform's mirror of Landau's function). Together with the decomposition direction, this says $g(n)$ is exactly the knapsack optimum over prime-power families. The injectivity hypothesis is essential: without distinct primes the claim is false (for example $t = \{2, 4\}$).
-- source:
--   Local lemma `prod_primePow_le_landauLocal` in the Landau (B) exploration (verified locally, not yet on the platform); the knapsack characterization of Landau's function, cf. Massias, Nicolas, Robin, Acta Arith. 50 (1988).

import Mathlib
import Definitions.Def_LandauExplore_landauLocal
import Definitions.Def_LandauFunction_landau
open Finset LandauExplore LandauFunction

namespace LandauCriterion
theorem converse_primePow_prod_le {n : ℕ} {t : Finset ℕ}
    (hf : ∃ f : ℕ → ℕ, (∀ q ∈ t, (f q).Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ q = (f q) ^ k) ∧ Set.InjOn f t)
    (hsum : ∑ q ∈ t, q ≤ n) : ∏ q ∈ t, q ≤ landauLocal n := by sorry
end LandauCriterion
