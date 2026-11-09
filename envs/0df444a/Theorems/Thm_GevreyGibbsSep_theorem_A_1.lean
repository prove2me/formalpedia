-- Prove2me | Theorems.Thm_GevreyGibbsSep_theorem_A_1
-- name    : GevreyGibbsSep.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:41:19.317013+00:00
-- url     : https://prove2.me/theorems/e51c7c27-e874-4aea-b574-f933a013f059
-- title:
--   Theorem A.1 — unique ground state of $\mathbb H_N$, $\varepsilon$-close to $|[e^{-\beta E/2}]_N\rangle$
-- statement:
--   Let $0<\tilde\varepsilon<1/2$ and $p=e^{-\beta E}/Z\in\mathscr W^s(\alpha,\xi,\rho)$, $s\ge1$. The choice
--   $$N\in\widetilde\Omega\Big(\frac{d+\xi}{\rho}\Big[ds+\log\frac{\alpha(1+\xi/\rho)}{\tilde\varepsilon}\Big]^s\Big)$$
--   with sufficiently large constants guarantees a unique ground state $|g\rangle$ of the discretized Witten Laplacian $\mathbb H_N$ with
--   $$0\le\lambda_0(\mathbb H_N)=\sigma_{\min}(\mathbb H_N)\le\frac{\tilde\varepsilon^2}{12\alpha\beta},\qquad \big\||[e^{-\beta E/2}]_N\rangle-|g\rangle\big\|\le\tilde\varepsilon .$$
--
--   The ground state of $\mathbb H_N$, which the quantum filter prepares, approximates the discretized square-root Gibbs state.
--
--   **Formalization Note** "Unique ground state" means that the least eigenvalue $\lambda_0$ has a one-dimensional eigenspace, spanned by the unit vector $g$; $\lambda_0$ is the minimum of the quadratic form on unit vectors.
--
--   Differences from the source:
--   - reading: $N\in\widetilde\Omega(F)$ with sufficiently large constants → there are $C>0$, $m\in\mathbb N$ depending only on $s$ such that the conclusion holds for every integer $N\ge C\cdot F\cdot\Lambda^m$, $\Lambda=\log(e+d+\alpha+\xi+\rho+1/\rho+1/\tilde\varepsilon)$; reason: the suppressed factors are polylogarithmic in these parameters (p.27) and larger $N$ only helps
--   - encoding: unique ground state $|g\rangle$ with $\lambda_0=\sigma_{\min}$ → a unit eigenvector $g$ for $\lambda_0$, $\lambda_0\|v\|^2\le\langle v,\mathbb H_Nv\rangle$ for all $v$, and every $\lambda_0$-eigenvector a multiple of $g$; reason: the same notions for a Hermitian positive semi-definite matrix, with a phase of $g$ chosen
--   - encoding: instances are Gibbs states $p=e^{-\beta E}/Z$ → instances are scaled potentials $V=\beta E$ with Gibbs state $e^{-V}/Z_V$; reason: two potentials with the same Gibbs state give the same oracle answers and the same target
--   - encoding: $p\in\mathscr W^s(\alpha,\xi,\rho)$, dimension $d$, $\beta>0$ → hypotheses $\alpha\ge1$, $\xi,\rho>0$, $d\ge1$, $\beta>0$; reason: the ranges of Definition 2 and of the setting
--   - encoding: $[\beta E]_{s,\rho}\le\xi$ with the supremum over $x\in[0,2\pi)^d$, and $\beta\Delta\le\log\alpha$ → $|\partial^aV(x)|\,\rho^{\|a\|_1}\le\xi\,(a!)^s$ for every $a\ne0$ and every $x\in\mathbb R^d$, and $V(x)-V(y)\le\log\alpha$ for all $x,y$; reason: equivalent for a continuous $2\pi$-periodic $V$: its values and derivatives on $\mathbb R^d$ are those on the period cell, where the maximum and minimum are attained
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem A.1, Eqs. (A58)–(A59), p.28

import Mathlib
import Definitions.Def_GevreyGibbsSep_GibbsClass
import Definitions.Def_GevreyGibbsSep_Grid
import Definitions.Def_GevreyGibbsSep_gridPt
import Definitions.Def_GevreyGibbsSep_HN
import Definitions.Def_GevreyGibbsSep_finiteGibbsState

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Theorem A.1, arXiv:2608.24527 (sha256 d4fd40eb…), Eqs. (A58)–(A59), p.28. Given
`0 < ε̃ < 1/2` and `p ∈ W^s(α, ξ, ρ)`, the choice `N ∈ Ω̃(((d + ξ)/ρ)[ds + log(α(1 + ξ/ρ)/ε̃)]^s)`
with sufficiently large constants guarantees a unique ground state `|g⟩` of `H_N` with
`0 ≤ λ₀(H_N) = σ_min(H_N) ≤ ε̃²/(12αβ)` and `‖|[e^{−βE/2}]_N⟩ − |g⟩‖ ≤ ε̃`.

**Formalization Note** `Ω̃` with sufficiently large constants is read as: there are `C > 0` and
`m ∈ ℕ` depending only on `s` such that the conclusion holds for every integer
`N ≥ C ((d + ξ)/ρ)(ds + log(α(1 + ξ/ρ)/ε̃))^s Λ^m`, `Λ = log(e + d + α + ξ + ρ + 1/ρ + 1/ε̃)`.
"Unique ground state" is: the least eigenvalue `λ₀` has a one-dimensional eigenspace spanned by
the unit vector `g` (a phase is chosen). `d ≥ 1` and the ranges of Definition 2 are hypotheses. -/
theorem theorem_A_1 :
    ∀ s : ℝ, 1 ≤ s → ∃ C : ℝ, ∃ m : ℕ, 0 < C ∧
    ∀ d : ℕ, 0 < d → ∀ α ξ ρ ε' β : ℝ, 1 ≤ α → 0 < ξ → 0 < ρ → 0 < ε' → ε' < 1 / 2 → 0 < β →
    ∀ E : (Fin d → ℝ) → ℝ, (fun x => β * E x) ∈ GibbsClass d s α ξ ρ →
    ∀ N : ℕ, 1 ≤ N →
      C * ((d + ξ) / ρ) * (d * s + Real.log (α * (1 + ξ / ρ) / ε')) ^ s
          * Real.log (Real.exp 1 + d + α + ξ + ρ + 1 / ρ + 1 / ε') ^ m ≤ N →
    ∃ (g : EuclideanSpace ℂ (Grid d N)) (lam0 : ℝ),
      ‖g‖ = 1 ∧
      Matrix.toEuclideanLin (HN d N β E) g = (lam0 : ℂ) • g ∧
      (∀ v : EuclideanSpace ℂ (Grid d N),
        lam0 * ‖v‖ ^ 2 ≤ RCLike.re ⟪v, Matrix.toEuclideanLin (HN d N β E) v⟫_ℂ) ∧
      (∀ v : EuclideanSpace ℂ (Grid d N),
        Matrix.toEuclideanLin (HN d N β E) v = (lam0 : ℂ) • v → ∃ c : ℂ, v = c • g) ∧
      0 ≤ lam0 ∧ lam0 ≤ ε' ^ 2 / (12 * α * β) ∧
      ‖finiteGibbsState (fun k => E (gridPt d N k)) β - g‖ ≤ ε' := by sorry

end GevreyGibbsSep
