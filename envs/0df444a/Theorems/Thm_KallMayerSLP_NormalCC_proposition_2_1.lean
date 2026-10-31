-- Prove2me | Theorems.Thm_KallMayerSLP_NormalCC_proposition_2_1
-- name    : KallMayerSLP.NormalCC.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:57.081298+00:00
-- url     : https://prove2.me/theorems/54e66e6a-420b-4a17-97c5-2be464ee36a7
-- title:
--   Proposition 2.1: $g$ and $G$ are pseudo-concave on $\{\mu^{\mathsf T}x>\mu_{n+1}\}$, pseudo-convex on $\{\mu^{\mathsf T}x<\mu_{n+1}\}$
-- statement:
--   The data are those of (2.28): $\tilde\zeta=(\tilde\zeta_1,\dots,\tilde\zeta_s)$ is a vector of independent standard normal random variables on the probability space $(\Omega,\mathcal F,\mathbb P)$, $D$ is an $n\times s$ matrix, $d\in\mathbb R^s$, $\mu\in\mathbb R^n$, $\mu_{n+1}\in\mathbb R$, and almost surely
--   $$\eta=D\tilde\zeta+\mu,\qquad \xi=d^{\mathsf T}\tilde\zeta+\mu_{n+1},$$
--   so that $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ is multivariate normal in the sense of Definition 2.1. $\|\cdot\|$ is the Euclidean norm, $\Phi$ the standard normal distribution function and $G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi)$.
--   Assume moreover that the distribution of $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ is non-degenerate, and put
--   $$g(x)=\frac{\mu^{\mathsf T}x-\mu_{n+1}}{\|D^{\mathsf T}x-d\|},$$
--   so that $G(x)=\Phi(g(x))$. Then both $g$ and $G$ are
--
--   1. pseudo-concave on the open half-space $\{x\mid\mu^{\mathsf T}x>\mu_{n+1}\}$, and
--   2. pseudo-convex on the open half-space $\{x\mid\mu^{\mathsf T}x<\mu_{n+1}\}$,
--
--   in the sense of Definition 1.2 (which includes continuous differentiability on the half-space). $G$ itself is neither quasi-concave nor quasi-convex on $\mathbb R^n$; the proposition recovers pseudo-concavity, useful for maximizing the reliability $G$, by restricting to half-spaces.
--
--   **Formalization Note** Pseudo-convexity of $f$ is stated as pseudo-concavity of $-f$, as in Definition 1.2.
--
--   Differences from the source:
--   - generalization: standing assumption of §2.3.2 (p.103): η is stochastic (no d ∈ ℝⁿ with η = d a.s.), which excludes n = 0 → n = 0 allowed (for n ≥ 1 non-degeneracy already makes η non-constant); reason: the statement remains true for n = 0 and specializes to the book's for n ≥ 1
--   - encoding: ζ = Bζ̃ + μ (random vectors, (2.25)/(2.28)) → ζ̃ on the same probability space, identity holds P-almost surely; reason: random vectors are identified up to null sets; probabilities, laws and moments are unchanged
--   - encoding: ζ = (ηᵀ, ξ)ᵀ ∈ ℝⁿ⁺¹ → Fin.snoc (η ω) (ξ ω) : Fin (n+1) → ℝ, ξ the last coordinate; reason: Lean convention; same object
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Proposition 2.1, p.109 (PDF p.119)

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector
import Definitions.Def_KallMayerSLP_NormalCC_IsNonDegenerateMultivariateNormal
import Definitions.Def_KallMayerSLP_NormalCC_probFun
import Definitions.Def_KallMayerSLP_NormalCC_IsPseudoConcaveOn

open MeasureTheory ProbabilityTheory Matrix

namespace KallMayerSLP.NormalCC

/-- **Proposition 2.1: `g` and `G` are pseudo-concave on `{μᵀx > μ_{n+1}}` and pseudo-convex on
`{μᵀx < μ_{n+1}}`** (Kall & Mayer 2005, Chapter 2, Proposition 2.1, p.109, PDF p.119).

The data are those of (2.28), p.105–106: `ζt = ζ̃` is a standard Gaussian vector in `ℝ^s`
(Definition 2.1), `D` an `(n × s)` matrix, `d ∈ ℝ^s`, `μ ∈ ℝⁿ`, `μn1 = μ_{n+1} ∈ ℝ`, and almost
surely `η = D ζ̃ + μ`, `ξ = dᵀ ζ̃ + μ_{n+1}`. `‖·‖` is the Euclidean norm, written
`Real.sqrt (∑ j, v j ^ 2)`.
In addition, the distribution of `ζ = (ηᵀ, ξ)ᵀ` is non-degenerate (p.104).

With `g(x) = (μᵀx − μ_{n+1}) / ‖Dᵀx − d‖` (p.109) and `G(x) = ℙ(ηᵀx ≥ ξ)`, both `g` and `G` are
a) pseudo-concave on the open half-space `{x | μᵀx > μ_{n+1}}` and
b) pseudo-convex (`−g`, `−G` pseudo-concave) on the open half-space `{x | μᵀx < μ_{n+1}}`,
in the sense of Definition 1.2 (p.88), which includes continuous differentiability on the set.

**Formalization Note.** `(ηᵀ, ξ)ᵀ` is `Fin.snoc (η ω) (ξ ω)`; `G = probFun P η ξ`. -/
theorem proposition_2_1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n s : ℕ}
    (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ) (ζt : Fin s → Ω → ℝ)
    (hζt : HighDimProb.RandomVectors.IsStandardGaussianVector P ζt)
    (D : Matrix (Fin n) (Fin s) ℝ) (d : Fin s → ℝ) (μ : Fin n → ℝ) (μn1 : ℝ)
    (hη : ∀ᵐ ω ∂P, η ω = D *ᵥ (fun j => ζt j ω) + μ)
    (hξ : ∀ᵐ ω ∂P, ξ ω = d ⬝ᵥ (fun j => ζt j ω) + μn1)
    (hnd : IsNonDegenerateMultivariateNormal P
      (fun ω => Fin.snoc (α := fun _ => ℝ) (η ω) (ξ ω))) :
    IsPseudoConcaveOn {x | μn1 < μ ⬝ᵥ x}
        (fun x => (μ ⬝ᵥ x - μn1) / Real.sqrt (∑ j, (Dᵀ *ᵥ x - d) j ^ 2)) ∧
    IsPseudoConcaveOn {x | μn1 < μ ⬝ᵥ x} (probFun P η ξ) ∧
    IsPseudoConcaveOn {x | μ ⬝ᵥ x < μn1}
        (fun x => -((μ ⬝ᵥ x - μn1) / Real.sqrt (∑ j, (Dᵀ *ᵥ x - d) j ^ 2))) ∧
    IsPseudoConcaveOn {x | μ ⬝ᵥ x < μn1} (fun x => -probFun P η ξ x) := by sorry

end KallMayerSLP.NormalCC
