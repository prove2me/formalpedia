-- Prove2me | Theorems.Thm_GreenTao_linear_forms_finite_indices
-- name    : GreenTao.linear_forms_finite_indices
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T21:16:16.523394+00:00
-- url     : https://prove2.me/theorems/72f4edc9-ec80-4cff-a6b8-095472beb0dc
-- title:
--   Linear-forms condition with arbitrary finite row and variable sets
-- statement:
--   Let $\nu_n$ satisfy the $(m_0,t_0,L_0)$ linear-forms condition. Let $I,J$ be finite sets with $|I|\le m_0$ and $|J|\le t_0$. Suppose rational coefficients $L_{ij}$ have numerator and denominator bounded in absolute value by $L_0$, each row is nonzero, and distinct rows are not rational multiples. For every sequence of translations $b_{n,i}$,
--
--   $$\mathbb E_{x\in(\mathbb Z/M_n\mathbb Z)^J}\prod_{i\in I}\nu_n\!\left(\sum_{j\in J}L_{ij}x_j+b_{n,i}\right)\longrightarrow1.$$
--
--   Rational coefficients are interpreted using the project's existing modular coefficient map. This is the existing linear-forms condition with arbitrary finite index sets, allowing direct use with cube vertices, faces, and disjoint unions of configurations.
--
--   **Formalization Note.** The finite variable set carries decidable equality so that Lean can construct its finite function space.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §3 Definition 3.1, equation (3.1). This theorem reindexes the project’s existing Fin-based condition using finite equivalences; it does not strengthen its hypotheses or bounds.

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib
open scoped BigOperators Topology
open Filter GreenTao

theorem GreenTao.linear_forms_finite_indices (M : ℕ → ℕ+) (ν : GreenTao.Family M) (m₀ t₀ L₀ : ℕ)
    (hν : GreenTao.LinearFormsCondition M ν m₀ t₀ L₀)
    (I J : Type) [Fintype I] [Fintype J] [DecidableEq J]
    (hm : Fintype.card I ≤ m₀) (ht : Fintype.card J ≤ t₀)
    (L : I → J → ℚ)
    (hL : ∀ i j, (L i j).num.natAbs ≤ L₀ ∧ (L i j).den ≤ L₀)
    (hnonzero : ∀ i, ∃ j, L i j ≠ 0)
    (hdistinct : ∀ i i', i ≠ i' → ¬ ∃ c : ℚ, ∀ j, L i j = c * L i' j)
    (b : ∀ n, I → ZMod (M n : ℕ)) :
    Tendsto (fun n => avg fun x : J → ZMod (M n : ℕ) =>
      ∏ i : I, ν n ((∑ j : J, ratCoeff (M n) (L i j) * x j) + b n i)) atTop (𝓝 1) := by sorry
