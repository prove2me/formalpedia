-- Prove2me | Theorems.Thm_KallMayerSLP_GenConcave_proposition_2_2_consequence
-- name    : KallMayerSLP.GenConcave.proposition_2_2_consequence
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:53.872695+00:00
-- url     : https://prove2.me/theorems/9df8643b-5749-4f85-83ad-8280b0a1a94e
-- title:
--   $\gamma$-concave laws have $\gamma$-concave $F_\xi$ and $H$, and convex joint probability constraints
-- statement:
--   Let the law $\mathbb P_\xi$ of the $r$-dimensional random vector $\xi$ be a $\gamma$-concave measure, let $F_\xi(y)=\mathbb P_\xi(\xi\le y)$ be its distribution function and $H(y)=\mathbb P_\xi(\xi\ge y)$ (componentwise order). Then
--
--   1. $F_\xi$ is $\gamma$-concave;
--   2. $H$ is $\gamma$-concave;
--   3. for every real $r\times n$ matrix $T$ and every $\alpha\in[0,1]$, the sets
--   $$
--   \{x\in\mathbb R^n\mid \mathbb P_\xi(Tx\ge\xi)\ge\alpha\}\quad\text{and}\quad\{x\in\mathbb R^n\mid \mathbb P_\xi(Tx\le\xi)\ge\alpha\}
--   $$
--   are convex.
--
--   Item 3 is the convexity of the feasible set $\mathcal B(\alpha)$ of the joint probability constraint (2.61) with random right-hand side, which is why $\gamma$-concavity of the law is the property sought in the rest of the section.
--
--   **Formalization Note** $\mathbb R^r$ is `Fin r → ℝ` with the componentwise order; $F_\xi(y)$ is the measure of `Set.Iic y` and $H(y)$ that of `Set.Ici y`.
--
--   Differences from the source:
--   - encoding: $T$ an $(s\times n)$ matrix and $\xi$ $s$-dimensional in (2.61) → $T$ an $(r\times n)$ matrix and $\xi$ $r$-dimensional; reason: the book uses both letters for the dimension of $\xi$ in §2.5; one letter here, same instances
--   - encoding: law $\mathbb P_\xi$ of a random vector $\xi$ → a measure $\mu$ on $\mathbb R^r$ ($\gamma$-concavity includes being a probability measure); reason: every probability measure is the law of the identity map, same instances
--   - generalization: §2.5.1 assumes throughout that $P_\xi$ is absolutely continuous (p.122) → any $\gamma$-concave probability measure, with or without a density; reason: the argument (Proposition 2.2 with $A=\mathbb R^r_\mp$) never uses the density, and the absolutely continuous laws are a special case
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §2.5.1, p.126 (PDF 136), consequences of Proposition 2.2; probability constraint (2.61), p.122 (PDF 132)

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveFun
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveMeasure

open MeasureTheory Matrix

namespace KallMayerSLP.GenConcave

/-- **Consequences of Proposition 2.2 for distribution functions** (Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 2, §2.5.1, p. 126, PDF p. 136, with the
probability constraint (2.61), p. 122, PDF p. 132). Let `ℙ_ξ` be `γ`-concave. Then
1. the distribution function `F_ξ(y) = ℙ_ξ(ξ ≤ y)` is `γ`-concave (Proposition 2.2 with
   `A = ℝ^r_−`), so `{x | ℙ_ξ(Tx ≥ ξ) ≥ α}` is convex for all `α ∈ [0, 1]`;
2. `H(y) = ℙ_ξ{y | ξ ≥ y}` is `γ`-concave (Proposition 2.2 with `A = ℝ^r_+`), so
   `{x | ℙ_ξ(Tx ≤ ξ) ≥ α}` is convex for all `α ∈ [0, 1]`.

**Formalization Note.** `ℝ^r = Fin r → ℝ` with the componentwise order; `F_ξ(y)` is
`μ (Set.Iic y)` and `H(y)` is `μ (Set.Ici y)`. `T` is an `(r × n)` real matrix (the book
writes `(s × n)` with `ξ` `s`-dimensional; here the dimension of `ξ` is `r` throughout), and
`Tx` is `T *ᵥ x`. -/
theorem proposition_2_2_consequence {r n : ℕ} (γ : EReal) (μ : Measure (Fin r → ℝ))
    (hμ : IsGammaConcaveMeasure γ μ) :
    IsGammaConcaveFun γ (fun y : Fin r → ℝ => (μ (Set.Iic y)).toReal) ∧
    IsGammaConcaveFun γ (fun y : Fin r → ℝ => (μ (Set.Ici y)).toReal) ∧
    ∀ (T : Matrix (Fin r) (Fin n) ℝ), ∀ α ∈ Set.Icc (0 : ℝ) 1,
      Convex ℝ {x : Fin n → ℝ | α ≤ (μ {ξ | ξ ≤ T *ᵥ x}).toReal} ∧
      Convex ℝ {x : Fin n → ℝ | α ≤ (μ {ξ | T *ᵥ x ≤ ξ}).toReal} := by sorry

end KallMayerSLP.GenConcave
