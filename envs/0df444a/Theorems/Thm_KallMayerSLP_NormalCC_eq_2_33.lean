-- Prove2me | Theorems.Thm_KallMayerSLP_NormalCC_eq_2_33
-- name    : KallMayerSLP.NormalCC.eq_2_33
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:58.986652+00:00
-- url     : https://prove2.me/theorems/27bc458e-b8c9-4937-a27a-75422ebd6a57
-- title:
--   (2.33): $G(x)\ge\alpha\iff\Phi^{-1}(\alpha)\|D^{\mathsf T}x-d\|-\mu^{\mathsf T}x\le-\mu_{n+1}$
-- statement:
--   The data are those of (2.28): $\tilde\zeta=(\tilde\zeta_1,\dots,\tilde\zeta_s)$ is a vector of independent standard normal random variables on the probability space $(\Omega,\mathcal F,\mathbb P)$, $D$ is an $n\times s$ matrix, $d\in\mathbb R^s$, $\mu\in\mathbb R^n$, $\mu_{n+1}\in\mathbb R$, and almost surely
--   $$\eta=D\tilde\zeta+\mu,\qquad \xi=d^{\mathsf T}\tilde\zeta+\mu_{n+1},$$
--   so that $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ is multivariate normal in the sense of Definition 2.1. $\|\cdot\|$ is the Euclidean norm, $\Phi$ the standard normal distribution function and $G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi)$.
--
--   Let $0<\alpha<1$. Then for every $x\in\mathbb R^n$:
--
--   1. if $D^{\mathsf T}x-d\neq0$, then $G(x)\ge\alpha\iff\Phi\big((\mu^{\mathsf T}x-\mu_{n+1})/\|D^{\mathsf T}x-d\|\big)\ge\alpha$;
--   2. in all cases (including $D^{\mathsf T}x-d=0$),
--   $$G(x)\ge\alpha\iff \Phi^{-1}(\alpha)\,\|D^{\mathsf T}x-d\|-\mu^{\mathsf T}x\le-\mu_{n+1}.$$
--
--   This is the deterministic equivalent of the separate chance constraint. For $\alpha\ge\frac12$, $\Phi^{-1}(\alpha)\ge0$ and the left-hand side is a convex function of $x$, which yields Theorem 2.5.
--
--   Differences from the source:
--   - generalization: standing assumption of §2.3.2 (p.103): η is stochastic, i.e. there is no d ∈ ℝⁿ with η = d a.s. (this also excludes n = 0) → not assumed; η may be a.s. constant and n = 0 is allowed; reason: the conclusion holds for every (η, ξ) of the stated form, and the book's case is the special case where η is not a.s. constant
--   - encoding: ζ = Bζ̃ + μ (random vectors, (2.25)/(2.28)) → ζ̃ on the same probability space, identity holds P-almost surely; reason: random vectors are identified up to null sets; probabilities, laws and moments are unchanged
--   - encoding: Φ⁻¹(α) (used without a range) → 0 < α < 1 assumed; Φ⁻¹ = normalQuantile = inf {q | Φ(q) ≥ α}; reason: Φ⁻¹(α) is a real number exactly for 0 < α < 1; outside that range the book's formula is undefined
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, eq. (2.33), p.106 (PDF p.116), and the remark at the top of p.107 (PDF p.117)

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector
import Definitions.Def_fd06_standardNormalCDF
import Definitions.Def_KallMayerSLP_NormalCC_probFun
import Definitions.Def_KallMayerSLP_NormalCC_normalQuantile

open MeasureTheory ProbabilityTheory Matrix

namespace KallMayerSLP.NormalCC

/-- **(2.33): deterministic equivalent of the chance constraint `G(x) ≥ α`** (Kall & Mayer 2005,
Chapter 2, (2.33), p.106, PDF p.116, with the remark on p.107, PDF p.117: "In the case when
`Dᵀx − d = 0`, the last inequality reduces to the first case in (2.32), consequently the
equivalence holds in all cases").

The data are those of (2.28), p.105–106: `ζt = ζ̃` is a standard Gaussian vector in `ℝ^s`
(Definition 2.1), `D` an `(n × s)` matrix, `d ∈ ℝ^s`, `μ ∈ ℝⁿ`, `μn1 = μ_{n+1} ∈ ℝ`, and almost
surely `η = D ζ̃ + μ`, `ξ = dᵀ ζ̃ + μ_{n+1}`. `‖·‖` is the Euclidean norm, written
`Real.sqrt (∑ j, v j ^ 2)`.

For `0 < α < 1` and every `x ∈ ℝⁿ`:
(1) if `Dᵀx − d ≠ 0`, then `G(x) ≥ α ⟺ Φ((μᵀx − μ_{n+1})/‖Dᵀx − d‖) ≥ α`;
(2) in all cases, `G(x) ≥ α ⟺ Φ⁻¹(α)‖Dᵀx − d‖ − μᵀx ≤ −μ_{n+1}`.

**Formalization Note.** `G = probFun P η ξ`; `Φ⁻¹ = normalQuantile`, which is the true inverse of
`Φ` exactly on `0 < α < 1`, the range where the book uses it. -/
theorem eq_2_33
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n s : ℕ}
    (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ) (ζt : Fin s → Ω → ℝ)
    (hζt : HighDimProb.RandomVectors.IsStandardGaussianVector P ζt)
    (D : Matrix (Fin n) (Fin s) ℝ) (d : Fin s → ℝ) (μ : Fin n → ℝ) (μn1 : ℝ)
    (hη : ∀ᵐ ω ∂P, η ω = D *ᵥ (fun j => ζt j ω) + μ)
    (hξ : ∀ᵐ ω ∂P, ξ ω = d ⬝ᵥ (fun j => ζt j ω) + μn1)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (x : Fin n → ℝ) :
    (Dᵀ *ᵥ x - d ≠ 0 → (α ≤ probFun P η ξ x ↔
      α ≤ FinancialDerivatives.FD06.standardNormalCDF
        ((μ ⬝ᵥ x - μn1) / Real.sqrt (∑ j, (Dᵀ *ᵥ x - d) j ^ 2)))) ∧
    (α ≤ probFun P η ξ x ↔
      normalQuantile α * Real.sqrt (∑ j, (Dᵀ *ᵥ x - d) j ^ 2) - μ ⬝ᵥ x ≤ -μn1) := by sorry

end KallMayerSLP.NormalCC
