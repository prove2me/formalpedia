-- Prove2me | Theorems.Thm_KallMayerSLP_ProbConstr_theorem_2_4
-- name    : KallMayerSLP.ProbConstr.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:16.208152+00:00
-- url     : https://prove2.me/theorems/e2e2c0be-f75e-4335-9455-ca4827bfbc18
-- title:
--   Theorem 2.4 (Kall), p.100 — $\mathcal B(\alpha)$ is convex for $\alpha>1-p_{i_1}$ when the smallest probability is unique
-- statement:
--   Let $\xi$ have the finite discrete distribution given by the realization tableau $(p_i;\hat\xi^i)_{i=1}^N$ with $p_i>0$ for all $i$ and $\sum_{i=1}^N p_i=1$, and let $I=\{1,\dots,N\}$. Let $p_{i_0}=\min_{i\in I}p_i$ and assume that the minimum is attained only at $i_0$. Let
--   $$
--   p_{i_1}=\min_{i\in I\setminus\{i_0\}}p_i
--   $$
--   be the second smallest probability. Then the feasible set $\mathcal B(\alpha)=\{x\mid \mathbb P_\xi(T(\xi)x\ge h(\xi))\ge\alpha\}$ is convex for every
--   $$
--   \alpha>1-p_{i_1}.
--   $$
--
--   This sharpens Marti's Theorem 2.3, whose threshold $1-p_{i_0}$ is larger: under a unique smallest probability, the joint probability constraint defines a convex set already at all levels above $1-p_{i_1}$.
--
--   **Formalization Note** Uniqueness of the minimizer is the hypothesis $p_{i_0}<p_i$ for all $i\ne i_0$; the index $i_1\ne i_0$ attains the minimum over $I\setminus\{i_0\}$, which forces $N\ge2$.
--
--   Differences from the source:
--   - generalization: T(ξ), h(ξ) affine in ξ (Notations, p.ix) → T(ξ), h(ξ) arbitrary functions of the realization; reason: only their values at the atoms ξ̂^i enter, and affine data are a special case
--   - encoding: ξ with the finite discrete distribution of the tableau (2.15), indices 1, …, N → τ : RealizationTableau N r with law Σ_i p_i δ_{ξ̂^i}, indices Fin N; reason: the same law; atoms are allowed to coincide, as in the book's tableau
--   - encoding: "p_{i₀} = min_{i∈I} p_i is uniquely determined; p_{i₁} = min_{i∈I∖{i₀}} p_i" → hypotheses ∀ i ≠ i₀, p_{i₀} < p_i; i₁ ≠ i₀; ∀ i ≠ i₀, p_{i₁} ≤ p_i; reason: the same conditions; i₁ ≠ i₀ makes N ≥ 2, which the minimum over I∖{i₀} needs (paper.md reading 7)
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.2, Theorem 2.4 (Kall 1976), p.100 (PDF 110)

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_feasibleSet
import Definitions.Def_KallMayerSLP_ProbConstr_RealizationTableau_measure

namespace KallMayerSLP.ProbConstr

/-- **Theorem 2.4** (Kall 1976). Let `p_{i₀} = min_{i∈I} p_i` and assume that `p_{i₀}` is uniquely
determined. Let `p_{i₁} = min_{i∈I∖{i₀}} p_i`. Then `B(α)` is convex for `α > 1 − p_{i₁}`.

Kall & Mayer 2005, Chapter 2, Theorem 2.4, p.100 (PDF 110) (proof cited: Kall [134]).

**Formalization Note.** `ξ` has the finite discrete distribution of the realization tableau (2.15)
(`τ.measure = Σ_i p_i · dirac(ξ̂^i)`, `p_i > 0`, `Σ p_i = 1`), indices `Fin N` for `1, …, N`. The data
`T(ξ)`, `h(ξ)` are arbitrary functions of the realization (the book's affine data are a special
case); only their values at the atoms matter. "`p_{i₀}` is the uniquely determined minimum" is
`∀ i ≠ i₀, p_{i₀} < p_i`; `i₁ ≠ i₀` attains the minimum over `I ∖ {i₀}`, so `N ≥ 2` (needed for
`p_{i₁}` to exist). Every real `α > 1 − p_{i₁}`. -/
theorem theorem_2_4 {N r m n : ℕ} (τ : RealizationTableau N r)
    (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ) (h : (Fin r → ℝ) → Fin m → ℝ) (i₀ i₁ : Fin N) (hi₀ : ∀ i, i ≠ i₀ → τ.p i₀ < τ.p i)
    (hi₁ : i₁ ≠ i₀) (hi₁min : ∀ i, i ≠ i₀ → τ.p i₁ ≤ τ.p i) (α : ℝ)
    (hα : 1 - τ.p i₁ < α) :
    Convex ℝ (feasibleSet τ.measure T h α) := by sorry

end KallMayerSLP.ProbConstr
