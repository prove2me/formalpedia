-- Prove2me | Theorems.Thm_KallMayerSLP_NormalCC_eq_2_36
-- name    : KallMayerSLP.NormalCC.eq_2_36
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:57.174994+00:00
-- url     : https://prove2.me/theorems/81775fc5-ca1e-4e6a-8fd5-93c452a6bf4f
-- title:
--   (2.36): deterministic equivalents of $G(x)\le\beta$ and $\hat G(x)\le\beta$ under non-degeneracy
-- statement:
--   The data are those of (2.28): $\tilde\zeta=(\tilde\zeta_1,\dots,\tilde\zeta_s)$ is a vector of independent standard normal random variables on the probability space $(\Omega,\mathcal F,\mathbb P)$, $D$ is an $n\times s$ matrix, $d\in\mathbb R^s$, $\mu\in\mathbb R^n$, $\mu_{n+1}\in\mathbb R$, and almost surely
--   $$\eta=D\tilde\zeta+\mu,\qquad \xi=d^{\mathsf T}\tilde\zeta+\mu_{n+1},$$
--   so that $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ is multivariate normal in the sense of Definition 2.1. $\|\cdot\|$ is the Euclidean norm, $\Phi$ the standard normal distribution function and $G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi)$.
--   Assume moreover that the distribution of $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ is non-degenerate. Let $0<\beta<1$. Then for every $x\in\mathbb R^n$
--   $$\mathbb P(\eta^{\mathsf T}x\ge\xi)\le\beta\iff\Phi^{-1}(\beta)\,\|D^{\mathsf T}x-d\|-\mu^{\mathsf T}x\ge-\mu_{n+1},$$
--   $$\mathbb P(\eta^{\mathsf T}x\le\xi)\le\beta\iff\Phi^{-1}(\beta)\,\|D^{\mathsf T}x-d\|+\mu^{\mathsf T}x\ge\mu_{n+1}.$$
--
--   For $\beta\le\frac12$ the left-hand sides are concave in $x$, so these reversed constraints define convex sets. Without non-degeneracy the equivalences fail at points with $D^{\mathsf T}x-d=0$.
--
--   Differences from the source:
--   - generalization: standing assumption of §2.3.2 (p.103): η is stochastic (no d ∈ ℝⁿ with η = d a.s.), which excludes n = 0 → n = 0 allowed (for n ≥ 1 non-degeneracy already makes η non-constant); reason: the statement remains true for n = 0 and specializes to the book's for n ≥ 1
--   - encoding: ζ = Bζ̃ + μ (random vectors, (2.25)/(2.28)) → ζ̃ on the same probability space, identity holds P-almost surely; reason: random vectors are identified up to null sets; probabilities, laws and moments are unchanged
--   - encoding: Φ⁻¹(β) (used without a range) → 0 < β < 1 assumed; Φ⁻¹ = normalQuantile = inf {q | Φ(q) ≥ β}; reason: Φ⁻¹(β) is a real number exactly for 0 < β < 1; outside that range the book's formula is undefined
--   - encoding: ζ = (ηᵀ, ξ)ᵀ ∈ ℝⁿ⁺¹ → Fin.snoc (η ω) (ξ ω) : Fin (n+1) → ℝ, ξ the last coordinate; reason: Lean convention; same object
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, eq. (2.36), p.108 (PDF p.118)

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector
import Definitions.Def_KallMayerSLP_NormalCC_IsNonDegenerateMultivariateNormal
import Definitions.Def_KallMayerSLP_NormalCC_probFun
import Definitions.Def_KallMayerSLP_NormalCC_normalQuantile

open MeasureTheory ProbabilityTheory Matrix

namespace KallMayerSLP.NormalCC

/-- **(2.36): deterministic equivalents of the reversed constraints `G(x) ≤ β`, `Ĝ(x) ≤ β` under
non-degeneracy** (Kall & Mayer 2005, Chapter 2, (2.36), p.108, PDF p.118: "Assuming
non-degeneracy of the probability distribution, we obtain the following equivalent representations
by reversing the inequalities in (2.35)").

The data are those of (2.28), p.105–106: `ζt = ζ̃` is a standard Gaussian vector in `ℝ^s`
(Definition 2.1), `D` an `(n × s)` matrix, `d ∈ ℝ^s`, `μ ∈ ℝⁿ`, `μn1 = μ_{n+1} ∈ ℝ`, and almost
surely `η = D ζ̃ + μ`, `ξ = dᵀ ζ̃ + μ_{n+1}`. `‖·‖` is the Euclidean norm, written
`Real.sqrt (∑ j, v j ^ 2)`.
In addition, the distribution of `ζ = (ηᵀ, ξ)ᵀ` is non-degenerate (p.104: its covariance matrix is
positive definite).

Then for `0 < β < 1` and every `x ∈ ℝⁿ`:
`ℙ(ηᵀx ≥ ξ) ≤ β ⟺ Φ⁻¹(β)‖Dᵀx − d‖ − μᵀx ≥ −μ_{n+1}`, and
`ℙ(ηᵀx ≤ ξ) ≤ β ⟺ Φ⁻¹(β)‖Dᵀx − d‖ + μᵀx ≥ μ_{n+1}`.

**Formalization Note.** `(ηᵀ, ξ)ᵀ ∈ ℝ^{n+1}` is `Fin.snoc (η ω) (ξ ω)` (`ξ` is the last coordinate).
`ℙ(ηᵀx ≥ ξ) = probFun P η ξ x`; `Φ⁻¹ = normalQuantile`, used only for `0 < β < 1`. -/
theorem eq_2_36
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n s : ℕ}
    (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ) (ζt : Fin s → Ω → ℝ)
    (hζt : HighDimProb.RandomVectors.IsStandardGaussianVector P ζt)
    (D : Matrix (Fin n) (Fin s) ℝ) (d : Fin s → ℝ) (μ : Fin n → ℝ) (μn1 : ℝ)
    (hη : ∀ᵐ ω ∂P, η ω = D *ᵥ (fun j => ζt j ω) + μ)
    (hξ : ∀ᵐ ω ∂P, ξ ω = d ⬝ᵥ (fun j => ζt j ω) + μn1)
    (hnd : IsNonDegenerateMultivariateNormal P
      (fun ω => Fin.snoc (α := fun _ => ℝ) (η ω) (ξ ω)))
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ) :
    (probFun P η ξ x ≤ β ↔
      -μn1 ≤ normalQuantile β * Real.sqrt (∑ j, (Dᵀ *ᵥ x - d) j ^ 2) - μ ⬝ᵥ x) ∧
    (P.real {ω | η ω ⬝ᵥ x ≤ ξ ω} ≤ β ↔
      μn1 ≤ normalQuantile β * Real.sqrt (∑ j, (Dᵀ *ᵥ x - d) j ^ 2) + μ ⬝ᵥ x) := by sorry

end KallMayerSLP.NormalCC
