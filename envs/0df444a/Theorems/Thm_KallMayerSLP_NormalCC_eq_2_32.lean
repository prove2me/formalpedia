-- Prove2me | Theorems.Thm_KallMayerSLP_NormalCC_eq_2_32
-- name    : KallMayerSLP.NormalCC.eq_2_32
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:37.304891+00:00
-- url     : https://prove2.me/theorems/564d8bbc-ed31-4fb2-8de7-a56ca2259ea2
-- title:
--   (2.32): closed form of $G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi)$ under a multivariate normal distribution
-- statement:
--   The data are those of (2.28): $\tilde\zeta=(\tilde\zeta_1,\dots,\tilde\zeta_s)$ is a vector of independent standard normal random variables on the probability space $(\Omega,\mathcal F,\mathbb P)$, $D$ is an $n\times s$ matrix, $d\in\mathbb R^s$, $\mu\in\mathbb R^n$, $\mu_{n+1}\in\mathbb R$, and almost surely
--   $$\eta=D\tilde\zeta+\mu,\qquad \xi=d^{\mathsf T}\tilde\zeta+\mu_{n+1},$$
--   so that $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ is multivariate normal in the sense of Definition 2.1. $\|\cdot\|$ is the Euclidean norm, $\Phi$ the standard normal distribution function and $G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi)$.
--
--   Then for every $x\in\mathbb R^n$
--   $$G(x)=\begin{cases}1,&\text{if }D^{\mathsf T}x-d=0\text{ and }\mu^{\mathsf T}x-\mu_{n+1}\ge0,\\[2pt]0,&\text{if }D^{\mathsf T}x-d=0\text{ and }\mu^{\mathsf T}x-\mu_{n+1}<0,\\[2pt]\Phi\!\left(\dfrac{\mu^{\mathsf T}x-\mu_{n+1}}{\|D^{\mathsf T}x-d\|}\right),&\text{if }D^{\mathsf T}x-d\neq0.\end{cases}$$
--
--   The formula turns the chance constraint into an explicit, deterministic function of the decision $x$; it is the basis of the deterministic equivalent (2.33).
--
--   Differences from the source:
--   - generalization: standing assumption of §2.3.2 (p.103): η is stochastic, i.e. there is no d ∈ ℝⁿ with η = d a.s. (this also excludes n = 0) → not assumed; η may be a.s. constant and n = 0 is allowed; reason: the conclusion holds for every (η, ξ) of the stated form, and the book's case is the special case where η is not a.s. constant
--   - encoding: ζ = Bζ̃ + μ (random vectors, (2.25)/(2.28)) → ζ̃ on the same probability space, identity holds P-almost surely; reason: random vectors are identified up to null sets; probabilities, laws and moments are unchanged
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, eqs. (2.31)–(2.32), p.106 (PDF p.116)

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector
import Definitions.Def_fd06_standardNormalCDF
import Definitions.Def_KallMayerSLP_NormalCC_probFun

open MeasureTheory ProbabilityTheory Matrix

namespace KallMayerSLP.NormalCC

/-- **(2.32): closed form of the probability function `G(x) = ℙ(ηᵀx ≥ ξ)`** (Kall & Mayer 2005,
Chapter 2, (2.31)–(2.32), p.106, PDF p.116).

The data are those of (2.28), p.105–106: `ζt = ζ̃` is a standard Gaussian vector in `ℝ^s`
(Definition 2.1), `D` an `(n × s)` matrix, `d ∈ ℝ^s`, `μ ∈ ℝⁿ`, `μn1 = μ_{n+1} ∈ ℝ`, and almost
surely `η = D ζ̃ + μ`, `ξ = dᵀ ζ̃ + μ_{n+1}`. `‖·‖` is the Euclidean norm, written
`Real.sqrt (∑ j, v j ^ 2)`.

Then, for every `x ∈ ℝⁿ`,
`G(x) = 1` if `Dᵀx − d = 0` and `μᵀx − μ_{n+1} ≥ 0`;
`G(x) = 0` if `Dᵀx − d = 0` and `μᵀx − μ_{n+1} < 0`;
`G(x) = Φ((μᵀx − μ_{n+1}) / ‖Dᵀx − d‖)` if `Dᵀx − d ≠ 0`,
where `Φ` is the standard normal distribution function
(`FinancialDerivatives.FD06.standardNormalCDF`).

**Formalization Note.** `G` is `probFun P η ξ`, defined as a probability, not by this formula. -/
theorem eq_2_32
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n s : ℕ}
    (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ) (ζt : Fin s → Ω → ℝ)
    (hζt : HighDimProb.RandomVectors.IsStandardGaussianVector P ζt)
    (D : Matrix (Fin n) (Fin s) ℝ) (d : Fin s → ℝ) (μ : Fin n → ℝ) (μn1 : ℝ)
    (hη : ∀ᵐ ω ∂P, η ω = D *ᵥ (fun j => ζt j ω) + μ)
    (hξ : ∀ᵐ ω ∂P, ξ ω = d ⬝ᵥ (fun j => ζt j ω) + μn1)
    (x : Fin n → ℝ) :
    (Dᵀ *ᵥ x - d = 0 → 0 ≤ μ ⬝ᵥ x - μn1 → probFun P η ξ x = 1) ∧
    (Dᵀ *ᵥ x - d = 0 → μ ⬝ᵥ x - μn1 < 0 → probFun P η ξ x = 0) ∧
    (Dᵀ *ᵥ x - d ≠ 0 → probFun P η ξ x =
      FinancialDerivatives.FD06.standardNormalCDF
        ((μ ⬝ᵥ x - μn1) / Real.sqrt (∑ j, (Dᵀ *ᵥ x - d) j ^ 2))) := by sorry

end KallMayerSLP.NormalCC
