-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
-- name    : Matrix.GeneralLinearGroup.exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/dbe0ee68-5d1b-53c0-b107-d6a2c0ab0975
-- title:
--   Conjugation-stable integral matrices force g ∈ K^× GLₙ(𝒪)
-- statement:
--   Let $K$ be a field, let $\mathcal O$ be a valuation subring of $K$, and let $n$ be a finite index type with decidable equality. Let $g$ be an element of the general linear group $\mathrm{GL}_n(K)$ and assume that conjugation by $g$ preserves entrywise integrality in the following sense: for every matrix $M \in M_n(K)$ all of whose entries $M_{ij}$ lie in $\mathcal O$, every entry of the product $g M g^{-1}$ lies in $\mathcal O$ (here $g$ and $g^{-1}$ are taken as matrices via the coercion from $\mathrm{GL}_n(K)$). The conclusion is the existence of a unit $c \in K^\times$ such that, entrywise, $c^{-1} g$ and $c g^{-1}$ are integral: for all indices $i, j$ one has $c^{-1} \cdot g_{ij} \in \mathcal O$, and for all indices $k, l$ one has $c \cdot (g^{-1})_{kl} \in \mathcal O$. Thus the assertion is stated purely entrywise, with no claim that $c^{-1}g$ is a unit of $M_n(\mathcal O)$, although the two integrality statements together express exactly that $g$ lies in $K^\times \cdot \mathrm{GL}_n(\mathcal O)$; only the stated one-sided integrality hypothesis on conjugation is assumed.
--
--   This is the computation underlying the description of the normaliser of the standard maximal order $M_n(\mathcal O)$ in $\mathrm{GL}_n(K)$ as $K^\times \mathrm{GL}_n(\mathcal O)$; over a local field it expresses the fact that the stabiliser of a vertex of the Bruhat–Tits building is the centre times a maximal compact subgroup. It is used in the Čeredník–Drinfeld part of the development, in the analysis of local boxes, of stabilisers and of the coset dictionary for Hecke sets at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
    {K : Type*} [Field K] (𝒪 : ValuationSubring K) {n : Type*} [Fintype n] [DecidableEq n]
    (g : GL n K)
    (hg : ∀ M : Matrix n n K, (∀ i j, M i j ∈ 𝒪) →
      ∀ i j, ((g : Matrix n n K) * M * ((g⁻¹ : GL n K) : Matrix n n K)) i j ∈ 𝒪) :
    ∃ c : Kˣ, (∀ i j, ((c⁻¹ : Kˣ) : K) * (g : Matrix n n K) i j ∈ 𝒪) ∧
      (∀ i j, (c : K) * ((g⁻¹ : GL n K) : Matrix n n K) i j ∈ 𝒪) := by sorry
