-- Prove2me | Theorems.Thm_KallMayerSLP_NormalCC_eq_2_30
-- name    : KallMayerSLP.NormalCC.eq_2_30
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:23.180624+00:00
-- url     : https://prove2.me/theorems/9a0dacc9-7c3c-4ec4-b8e4-fc9f18452e5e
-- title:
--   (2.29)–(2.30): $\eta^{\mathsf T}x-\xi$ is normal with mean $\mu^{\mathsf T}x-\mu_{n+1}$ and variance $\|D^{\mathsf T}x-d\|^2$
-- statement:
--   The data are those of (2.28): $\tilde\zeta=(\tilde\zeta_1,\dots,\tilde\zeta_s)$ is a vector of independent standard normal random variables on the probability space $(\Omega,\mathcal F,\mathbb P)$, $D$ is an $n\times s$ matrix, $d\in\mathbb R^s$, $\mu\in\mathbb R^n$, $\mu_{n+1}\in\mathbb R$, and almost surely
--   $$\eta=D\tilde\zeta+\mu,\qquad \xi=d^{\mathsf T}\tilde\zeta+\mu_{n+1},$$
--   so that $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ is multivariate normal in the sense of Definition 2.1. $\|\cdot\|$ is the Euclidean norm, $\Phi$ the standard normal distribution function and $G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi)$.
--
--   Then for every $x\in\mathbb R^n$ the random variable $\zeta(x,\eta,\xi)=\eta^{\mathsf T}x-\xi$ satisfies:
--
--   1. (2.29) $\zeta(x,\eta,\xi)=\tilde\zeta^{\mathsf T}(D^{\mathsf T}x-d)+\mu^{\mathsf T}x-\mu_{n+1}$ almost surely;
--   2. $\zeta(x,\eta,\xi)$ is normally distributed with mean $\mu^{\mathsf T}x-\mu_{n+1}$ and variance $\|D^{\mathsf T}x-d\|^2$ (a point mass when the variance is $0$);
--   3. (2.30) $\zeta(x,\eta,\xi)$ is integrable, $\mathbb E[\zeta(x,\eta,\xi)]=\mu^{\mathsf T}x-\mu_{n+1}$ and
--   $$\operatorname{Var}[\zeta(x,\eta,\xi)]=\|D^{\mathsf T}x-d\|^2=x^{\mathsf T}DD^{\mathsf T}x-2(Dd)^{\mathsf T}x+\|d\|^2 .$$
--
--   This is the starting point of the explicit formula (2.32) for $G$.
--
--   **Formalization Note** "Normal with mean $m$ and variance $v$" is the law $\mathcal N(m,v)$ (`gaussianReal`), which for $v=0$ is the Dirac mass at $m$.
--
--   Differences from the source:
--   - generalization: standing assumption of §2.3.2 (p.103): η is stochastic, i.e. there is no d ∈ ℝⁿ with η = d a.s. (this also excludes n = 0) → not assumed; η may be a.s. constant and n = 0 is allowed; reason: the conclusion holds for every (η, ξ) of the stated form, and the book's case is the special case where η is not a.s. constant
--   - encoding: ζ = Bζ̃ + μ (random vectors, (2.25)/(2.28)) → ζ̃ on the same probability space, identity holds P-almost surely; reason: random vectors are identified up to null sets; probabilities, laws and moments are unchanged
--   - encoding: ζ(x, η, ξ) is normally distributed (with Var = 0 meaning ζ = 𝔼ζ a.s.) → law of ηᵀx − ξ equals gaussianReal (mean) (variance), the Dirac mass when the variance is 0; reason: Mathlib's normal law includes the degenerate case, exactly as the book's remark on p.106
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, eqs. (2.29)–(2.30), p.106 (PDF p.116)

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector

open MeasureTheory ProbabilityTheory Matrix

namespace KallMayerSLP.NormalCC

/-- **(2.29)–(2.30): the random variable `ζ(x, η, ξ) = ηᵀx − ξ` is normal with mean
`μᵀx − μ_{n+1}` and variance `‖Dᵀx − d‖²`** (Kall & Mayer 2005, Chapter 2, (2.29)–(2.30),
p.106, PDF p.116).

The data are those of (2.28), p.105–106: `ζt = ζ̃` is a standard Gaussian vector in `ℝ^s`
(Definition 2.1), `D` an `(n × s)` matrix, `d ∈ ℝ^s`, `μ ∈ ℝⁿ`, `μn1 = μ_{n+1} ∈ ℝ`, and almost
surely `η = D ζ̃ + μ`, `ξ = dᵀ ζ̃ + μ_{n+1}`. `‖·‖` is the Euclidean norm, written
`Real.sqrt (∑ j, v j ^ 2)`.

Conclusion, for every `x ∈ ℝⁿ`: (1) (2.29) `ζ(x, η, ξ) = ζ̃ᵀ(Dᵀx − d) + μᵀx − μ_{n+1}` a.s.;
(2) `ζ(x, η, ξ)` is normally distributed with mean `μᵀx − μ_{n+1}` and variance `‖Dᵀx − d‖²`
(degenerate, i.e. a point mass, when the variance is `0`); (3) `ζ` is integrable and
`𝔼[ζ] = μᵀx − μ_{n+1}`;
(4) `Var[ζ] = ‖Dᵀx − d‖²`; (5) `‖Dᵀx − d‖² = xᵀDDᵀx − 2(Dd)ᵀx + ‖d‖²`.

**Formalization Note.** "Normally distributed with variance `v`" is `P.map ζ = gaussianReal m v`
(Mathlib's `gaussianReal m 0` is the Dirac mass at `m`). `𝔼` is the Bochner integral and `Var`
is Mathlib's `variance`. -/
theorem eq_2_30
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n s : ℕ}
    (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ) (ζt : Fin s → Ω → ℝ)
    (hζt : HighDimProb.RandomVectors.IsStandardGaussianVector P ζt)
    (D : Matrix (Fin n) (Fin s) ℝ) (d : Fin s → ℝ) (μ : Fin n → ℝ) (μn1 : ℝ)
    (hη : ∀ᵐ ω ∂P, η ω = D *ᵥ (fun j => ζt j ω) + μ)
    (hξ : ∀ᵐ ω ∂P, ξ ω = d ⬝ᵥ (fun j => ζt j ω) + μn1)
    (x : Fin n → ℝ) :
    (∀ᵐ ω ∂P, η ω ⬝ᵥ x - ξ ω = (fun j => ζt j ω) ⬝ᵥ (Dᵀ *ᵥ x - d) + μ ⬝ᵥ x - μn1) ∧
    P.map (fun ω => η ω ⬝ᵥ x - ξ ω) =
      gaussianReal (μ ⬝ᵥ x - μn1) (∑ j, (Dᵀ *ᵥ x - d) j ^ 2).toNNReal ∧
    Integrable (fun ω => η ω ⬝ᵥ x - ξ ω) P ∧
    ∫ ω, (η ω ⬝ᵥ x - ξ ω) ∂P = μ ⬝ᵥ x - μn1 ∧
    variance (fun ω => η ω ⬝ᵥ x - ξ ω) P = ∑ j, (Dᵀ *ᵥ x - d) j ^ 2 ∧
    ∑ j, (Dᵀ *ᵥ x - d) j ^ 2 = x ⬝ᵥ ((D * Dᵀ) *ᵥ x) - 2 * ((D *ᵥ d) ⬝ᵥ x) + ∑ j, d j ^ 2 := by sorry

end KallMayerSLP.NormalCC
