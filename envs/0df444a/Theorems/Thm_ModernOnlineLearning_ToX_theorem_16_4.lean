-- Prove2me | Theorems.Thm_ModernOnlineLearning_ToX_theorem_16_4
-- name    : ModernOnlineLearning.ToX.theorem_16_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:29.888243+00:00
-- url     : https://prove2.me/theorems/0a730c13-e99f-4263-a91a-0b6be9d44a5c
-- title:
--   Theorem 16.4 — online linear regret bounds empirical Rademacher complexity
-- statement:
--   Let $Z\subseteq\mathbb R^d$ be symmetric under negation, let $z_1,\ldots,z_T\in Z$, and let $V\subseteq\mathbb R^d$ be nonempty, bounded and closed. Suppose a deterministic online algorithm chooses $x_t\in V$ using only past gradients and has regret at most $R(T)$ for every sequence of linear loss gradients in $Z$. For the class $H_{\mathrm{lin}}=\{z\mapsto\langle x,z\rangle:x\in V\}$,
--
--   $$
--   \widehat{\mathfrak R}_S(H_{\mathrm{lin}})
--   =\frac1T\mathbb E_\varepsilon\left[\sup_{x\in V}\sum_{t=1}^T\varepsilon_t\langle x,z_t\rangle\right]
--   \le\frac{R(T)}T.
--   $$
--
--   This reduction turns any uniform online linear regret bound into a bound on the complexity of the same linear class.
--
--   **Formalization Note** The algorithm is deterministic and nonanticipating; the book also permits independent internal randomization. The sample is indexed from one and $T\ge1$. The real supremum is taken over exactly $V$; boundedness and nonemptiness rule out default values on unbounded or empty sets.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 16.4, p. 272, displays (16.3)–(16.4)

import Mathlib
import Definitions.Def_ModernOnlineLearning_ToX_Algorithms

namespace ModernOnlineLearning.ToX

/-- Theorem 16.4, p. 272: a deterministic non-anticipating online linear
algorithm with worst-case regret at most `R T` bounds the empirical
Rademacher complexity of the linear class indexed by `V`. -/
theorem theorem_16_4 {d T : ℕ} (hT : 1 ≤ T)
    (Z V : Set (Fin d → ℝ)) (z : ℕ → Fin d → ℝ)
    (hZsym : ∀ a ∈ Z, -a ∈ Z)
    (hz : ∀ t ∈ Finset.Icc 1 T, z t ∈ Z)
    (hVne : V.Nonempty) (hVbd : Bornology.IsBounded V) (hVclosed : IsClosed V)
    (R : ℕ → ℝ) (A : (ℕ → Fin d → ℝ) → ℕ → Fin d → ℝ)
    (hA : IsOnlineAlgorithm T Z V (R T) A) :
    empiricalRadLinear (T := T) V hT ⟨hVne, hVbd⟩ z ≤ R T / (T : ℝ) := by sorry

end ModernOnlineLearning.ToX
