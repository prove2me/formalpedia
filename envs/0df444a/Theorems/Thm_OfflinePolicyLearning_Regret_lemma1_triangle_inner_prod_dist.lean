-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Regret_lemma1_triangle_inner_prod_dist
-- name    : OfflinePolicyLearning.Regret.lemma1_triangle_inner_prod_dist
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:49.244953+00:00
-- url     : https://prove2.me/theorems/37f36250-5207-4dd8-8d57-72ac81a01cd1
-- title:
--   Lemma 1 (1), p. 15 — the inner product distance satisfies I_Γ(π₁,π₂) ≤ I_Γ(π₁,π₃) + I_Γ(π₃,π₂)
-- statement:
--   Let $\Pi$ be a policy class, $x_1,\dots,x_n\in\mathcal X$ points and $\gamma_1,\dots,\gamma_n\in\mathbb R^d$ weights, and let $I_\Gamma$ be the inner product distance of Definition 6 (actions identified with basis vectors, so $\langle\gamma_i,\pi(x_i)\rangle=\gamma_{i,\pi(x_i)}$). For all $\pi_1,\pi_2,\pi_3\in\Pi$,
--   $$I_\Gamma(\pi_1,\pi_2)\le I_\Gamma(\pi_1,\pi_3)+I_\Gamma(\pi_3,\pi_2).$$
--
--   Together with symmetry this makes $I_\Gamma$ a pseudometric on $\Pi$, which is how the paper's chaining argument uses it.
--
--   **Formalization Note** Only part 1 of Lemma 1 is posed; part 2 ($N_{I_\Gamma}(\varepsilon,\Pi,\{x_1,\dots,x_n\})\le N_H(\varepsilon^2,\Pi)$) is false as printed (a three-point counterexample is recorded in the mission description). The convention $0/0=0$ is Lean's division by zero.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 15, Lemma 1 (1)

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace OfflinePolicyLearning.Regret
theorem lemma1_triangle_inner_prod_dist {X : Type*} {d n : ℕ} (Pol : Set (X → Fin d))
    (x : Fin n → X) (γ : Fin n → Fin d → ℝ) (π₁ π₂ π₃ : X → Fin d)
    (h₁ : π₁ ∈ Pol) (h₂ : π₂ ∈ Pol) (h₃ : π₃ ∈ Pol) :
    innerProdDist Pol x γ π₁ π₂ ≤ innerProdDist Pol x γ π₁ π₃ + innerProdDist Pol x γ π₃ π₂ := by sorry
end OfflinePolicyLearning.Regret
