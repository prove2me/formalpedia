-- Prove2me | Theorems.Thm_KallMayerSLP_NormalCC_eq_2_34_2_35
-- name    : KallMayerSLP.NormalCC.eq_2_34_2_35
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:51.218416+00:00
-- url     : https://prove2.me/theorems/67c654b6-6e97-4b7a-80b0-eececce624a5
-- title:
--   (2.34)–(2.35): closed form and deterministic equivalent of $\hat G(x)=\mathbb P(\eta^{\mathsf T}x\le\xi)$
-- statement:
--   The data are those of (2.28): $\tilde\zeta=(\tilde\zeta_1,\dots,\tilde\zeta_s)$ is a vector of independent standard normal random variables on the probability space $(\Omega,\mathcal F,\mathbb P)$, $D$ is an $n\times s$ matrix, $d\in\mathbb R^s$, $\mu\in\mathbb R^n$, $\mu_{n+1}\in\mathbb R$, and almost surely
--   $$\eta=D\tilde\zeta+\mu,\qquad \xi=d^{\mathsf T}\tilde\zeta+\mu_{n+1},$$
--   so that $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ is multivariate normal in the sense of Definition 2.1. $\|\cdot\|$ is the Euclidean norm, $\Phi$ the standard normal distribution function and $G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi)$.
--
--   Let $\hat G(x)=\mathbb P(\eta^{\mathsf T}x\le\xi)$. Then for every $x\in\mathbb R^n$:
--
--   1. (2.34)
--   $$\hat G(x)=\begin{cases}1,&\text{if }D^{\mathsf T}x-d=0\text{ and }\mu^{\mathsf T}x-\mu_{n+1}\le0,\\[2pt]0,&\text{if }D^{\mathsf T}x-d=0\text{ and }\mu^{\mathsf T}x-\mu_{n+1}>0,\\[2pt]\Phi\!\left(\dfrac{-\mu^{\mathsf T}x+\mu_{n+1}}{\|D^{\mathsf T}x-d\|}\right),&\text{if }D^{\mathsf T}x-d\neq0;\end{cases}$$
--   2. (2.35, second line) for every $0<\alpha<1$,
--   $$\mathbb P(\eta^{\mathsf T}x\le\xi)\ge\alpha\iff\Phi^{-1}(\alpha)\,\|D^{\mathsf T}x-d\|+\mu^{\mathsf T}x\le\mu_{n+1}.$$
--
--   The first line of (2.35), for $\mathbb P(\eta^{\mathsf T}x\ge\xi)$, is (2.33).
--
--   Differences from the source:
--   - generalization: standing assumption of §2.3.2 (p.103): η is stochastic, i.e. there is no d ∈ ℝⁿ with η = d a.s. (this also excludes n = 0) → not assumed; η may be a.s. constant and n = 0 is allowed; reason: the conclusion holds for every (η, ξ) of the stated form, and the book's case is the special case where η is not a.s. constant
--   - encoding: ζ = Bζ̃ + μ (random vectors, (2.25)/(2.28)) → ζ̃ on the same probability space, identity holds P-almost surely; reason: random vectors are identified up to null sets; probabilities, laws and moments are unchanged
--   - encoding: Φ⁻¹(α) (used without a range) → 0 < α < 1 assumed; Φ⁻¹ = normalQuantile = inf {q | Φ(q) ≥ α}; reason: Φ⁻¹(α) is a real number exactly for 0 < α < 1; outside that range the book's formula is undefined
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, eq. (2.34), p.107 (PDF p.117), and eq. (2.35), p.108 (PDF p.118)

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector
import Definitions.Def_fd06_standardNormalCDF
import Definitions.Def_KallMayerSLP_NormalCC_normalQuantile

open MeasureTheory ProbabilityTheory Matrix

namespace KallMayerSLP.NormalCC

/-- **(2.34)–(2.35): the reversed probability function `Ĝ(x) = ℙ(ηᵀx ≤ ξ)` and its deterministic
equivalent** (Kall & Mayer 2005, Chapter 2, (2.34), p.107, PDF p.117, and (2.35), second line,
p.108, PDF p.118).

The data are those of (2.28), p.105–106: `ζt = ζ̃` is a standard Gaussian vector in `ℝ^s`
(Definition 2.1), `D` an `(n × s)` matrix, `d ∈ ℝ^s`, `μ ∈ ℝⁿ`, `μn1 = μ_{n+1} ∈ ℝ`, and almost
surely `η = D ζ̃ + μ`, `ξ = dᵀ ζ̃ + μ_{n+1}`. `‖·‖` is the Euclidean norm, written
`Real.sqrt (∑ j, v j ^ 2)`.

Let `Ĝ(x) = ℙ(ηᵀx ≤ ξ)`. Then for every `x ∈ ℝⁿ`:
(1) (2.34) `Ĝ(x) = 1` if `Dᵀx − d = 0` and `μᵀx − μ_{n+1} ≤ 0`; `Ĝ(x) = 0` if `Dᵀx − d = 0`
and `μᵀx − μ_{n+1} > 0`; `Ĝ(x) = Φ((−μᵀx + μ_{n+1})/‖Dᵀx − d‖)` if `Dᵀx − d ≠ 0`;
(2) (2.35) for `0 < α < 1`: `ℙ(ηᵀx ≤ ξ) ≥ α ⟺ Φ⁻¹(α)‖Dᵀx − d‖ + μᵀx ≤ μ_{n+1}`.

(The first line of (2.35), for `ℙ(ηᵀx ≥ ξ)`, is (2.33): `KallMayerSLP.NormalCC.eq_2_33`.)

**Formalization Note.** `Ĝ(x)` is written out as `P.real {ω | η ω ⬝ᵥ x ≤ ξ ω}`;
`Φ⁻¹ = normalQuantile` is used only for `0 < α < 1`. -/
theorem eq_2_34_2_35
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n s : ℕ}
    (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ) (ζt : Fin s → Ω → ℝ)
    (hζt : HighDimProb.RandomVectors.IsStandardGaussianVector P ζt)
    (D : Matrix (Fin n) (Fin s) ℝ) (d : Fin s → ℝ) (μ : Fin n → ℝ) (μn1 : ℝ)
    (hη : ∀ᵐ ω ∂P, η ω = D *ᵥ (fun j => ζt j ω) + μ)
    (hξ : ∀ᵐ ω ∂P, ξ ω = d ⬝ᵥ (fun j => ζt j ω) + μn1)
    (x : Fin n → ℝ) :
    (Dᵀ *ᵥ x - d = 0 → μ ⬝ᵥ x - μn1 ≤ 0 → P.real {ω | η ω ⬝ᵥ x ≤ ξ ω} = 1) ∧
    (Dᵀ *ᵥ x - d = 0 → 0 < μ ⬝ᵥ x - μn1 → P.real {ω | η ω ⬝ᵥ x ≤ ξ ω} = 0) ∧
    (Dᵀ *ᵥ x - d ≠ 0 → P.real {ω | η ω ⬝ᵥ x ≤ ξ ω} =
      FinancialDerivatives.FD06.standardNormalCDF
        ((-(μ ⬝ᵥ x) + μn1) / Real.sqrt (∑ j, (Dᵀ *ᵥ x - d) j ^ 2))) ∧
    (∀ α : ℝ, 0 < α → α < 1 → (α ≤ P.real {ω | η ω ⬝ᵥ x ≤ ξ ω} ↔
      normalQuantile α * Real.sqrt (∑ j, (Dᵀ *ᵥ x - d) j ^ 2) + μ ⬝ᵥ x ≤ μn1)) := by sorry

end KallMayerSLP.NormalCC
