-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
-- name    : LanglandsTunnell.RankinSelberg.forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/0b8902f4-2f0c-52dd-8606-2b8aadf20aba
-- title:
--   Local level invariance at p depends only on vₚ(N)
-- statement:
--   Let $p$ be a height-one prime of the ring of integers $\mathcal{O}_{\mathbb{Q}}$, let $N$ be an ideal of $\mathcal{O}_{\mathbb{Q}}$, and let $w_2^{\mathrm{base}}$ be an arbitrary complex-valued function on $\mathrm{GL}_2$ of the completion of $\mathbb{Q}$ at $p$. Here, for an ideal $M$, the local level group [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at $p$ of level $M$ is the preimage, under the monoid homomorphism [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) placing a matrix at the component $p$ of the finite adele ring, of the subgroup `AdelicLevel.finiteLevelOne` of $\mathrm{GL}_2$ of the finite adeles consisting of those $g$ for which both $g$ and $g^{-1}$ satisfy the predicate `AdelicLevel.IsLevelOneMatrix` at level $M$. Assume that $w_2^{\mathrm{base}}(gk) = w_2^{\mathrm{base}}(g)$ for every $k$ in the local level group of level $N$ at $p$ and every $g$, and let $b$ be a natural number with $p^b \mid N$ and $p^{b+1} \nmid N$. Then $w_2^{\mathrm{base}}(gk) = w_2^{\mathrm{base}}(g)$ for all $g$ and all $k$ in the local level group of level $p^b$ at $p$.
--
--   This records the standard fact that the local component at $p$ of a level-one (i.e. $K_1$-type) congruence subgroup sees only the exponent of $p$ in the level, so that right invariance of a local vector under the level-$N$ group at $p$ is the same as right invariance under the level-$p^b$ group when $p^b$ exactly divides $N$. It is used to transfer the local component at $p$ of a global form of level $N$ into the level $p^b$ in which the local Rankin–Selberg integrals and their functional equations are formulated, and is cited by several of the local integral computations in that part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq.lean

import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.RankinSelberg.forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ))
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N) :
    ∀ (k g : GL (Fin 2) (p.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) → w₂base (g * k) = w₂base g := by sorry
