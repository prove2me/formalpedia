-- Prove2me | Theorems.Thm_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
-- name    : NumberField.exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/a14d879a-3e95-5ced-aeaf-8f31ca9bea49
-- title:
--   Prescribed signs for integers congruent to 1 mod 𝔪
-- statement:
--   Let $K$ be a field which is a number field (so $\mathcal O_K = \mathcal{O}\,K$ denotes its ring of integers), let $\mathfrak m$ be an ideal of $\mathcal O_K$ with $\mathfrak m \neq \bot$, i.e. $\mathfrak m$ is non-zero, and let $N$ be an arbitrary subset of the set of ring homomorphisms $K \to \mathbb R$, that is, of the real embeddings of $K$. The assertion is that there exists an element $\alpha$ of $\mathcal O_K$ such that $\alpha \neq 0$, such that $\alpha - 1$ lies in $\mathfrak m$ (equivalently $\alpha \equiv 1 \pmod{\mathfrak m}$), and such that for every real embedding $\varphi \colon K \to \mathbb R$ one has $\varphi(\alpha) < 0$ if and only if $\varphi \in N$, where $\alpha$ is viewed in $K$ via the structure map $\mathcal O_K \to K$. Thus the prescribed sign pattern is realised exactly: $\varphi(\alpha)$ is negative precisely at the embeddings belonging to $N$ and positive or zero elsewhere; since $\alpha \neq 0$ and $\varphi$ is injective, $\varphi(\alpha)$ is in fact non-zero for every $\varphi$.
--
--   This is the surjectivity of the sign map from the group of elements of $\mathcal O_K$ congruent to $1$ modulo $\mathfrak m$ onto $\prod_{\varphi \text{ real}} \{\pm 1\}$, the archimedean ingredient in comparing ray class groups modulo $\mathfrak m$ and modulo $\mathfrak m\infty$. It is used in the construction and computation of the idelic Artin map for abelian extensions, where archimedean signs must be attached to a ray class character with prescribed conductor behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
    (K : Type*) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥)
    (N : Set (K →+* ℝ)) :
    ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔪 ∧
      ∀ φ : K →+* ℝ, φ (algebraMap (𝓞 K) K α) < 0 ↔ φ ∈ N := by sorry
