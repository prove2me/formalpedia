-- Prove2me | Theorems.Thm_HasSum_fin_prod
-- name    : HasSum.fin_prod
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:45.362684+00:00
-- url     : https://prove2.me/theorems/26cf3069-b8c7-45af-b8ad-3eb58be28e96
-- title:
--   A finite product of summable nonnegative families sums to the product of the sums
-- statement:
--   Fix $R \in \mathbb{N}$ and for each $i \in \{0, \dots, R-1\}$ let
--   $f_i : \mathbb{N} \to \mathbb{R}$ be a nonnegative family, $f_i(n) \ge 0$, which is summable
--   with sum $a_i$. Consider the family indexed by $R$-tuples of naturals that takes the product of
--   one term from each factor,
--
--   $$
--   n = (n_0, \dots, n_{R-1}) \;\longmapsto\; \prod_{i} f_i(n_i).
--   $$
--
--   Then this family is summable with
--
--   $$
--   \sum_{n \in \mathbb{N}^{R}} \ \prod_{i} f_i(n_i) \;=\; \prod_{i} a_i .
--   $$
--
--   Summation over a product index set factorizes into a product of sums. This is the statement
--   behind every product-form result: in a Jackson or Kelly network the stationary distribution is a
--   product of per-queue terms, and the normalizing constant is computed exactly by this
--   factorization. Nonnegativity is what makes the unordered sum over $\mathbb{N}^R$
--   unconditional.
--
--   **Formalization Note** Summability is `HasSum`, the index type is `Fin R → ℕ`, and the
--   product is `Finset.prod` over `Finset.univ : Finset (Fin R)`.
-- source:
--   Iterated form of the product rule for summable families; cf. Mathlib `HasSum.mul_eq`. Carved from the accepted proof of KellyStochasticNetworks.open_migration_equilibrium, https://prove2.me/submissions/28ecb8c2-195c-4add-ad43-10520f339e62

import Mathlib

open Finset

theorem HasSum.fin_prod (R : ℕ) : ∀ (f : Fin R → ℕ → ℝ) (a : Fin R → ℝ),
    (∀ i n, 0 ≤ f i n) → (∀ i, HasSum (f i) (a i)) →
    HasSum (fun n : Fin R → ℕ => ∏ i, f i (n i)) (∏ i, a i) := by sorry
