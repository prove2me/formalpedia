-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_eq_4_32
-- name    : LogGammaPolymer.Variance.eq_4_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:59.809987+00:00
-- url     : https://prove2.me/theorems/744f41a1-a414-4ca4-a13d-15b10f16accb
-- title:
--   (4.32), proof of Theorem 2.1 (upper bound) — E(ξ_x) ≤ CN^{2/3} under (4.9)
-- statement:
--   Assume (2.4) with $0<\theta<\mu$, a real scaling parameter $N\ge1$, and rectangle dimensions $(m,n)\in\mathbb N^2$ with
--   $$|m-N\Psi_1(\mu-\theta)|\le\kappa_N\quad\text{and}\quad|n-N\Psi_1(\theta)|\le\kappa_N\qquad(4.9)$$
--   for a sequence $\kappa_N\le C_\kappa N^{2/3}$ with a fixed constant $C_\kappa<\infty$. Then there is a constant $C$ such that
--   $$E(\xi_x)\le CN^{2/3}\qquad(4.32)$$
--   for all $N\ge1$, where $E$ is the annealed expectation. A single constant works for $0<\theta<\mu$ that vary in a compact set.
--
--   Combined with (3.18) and (4.24), this gives the upper variance bound (4.33), $\mathrm{Var}[\log Z_{m,n}]\le CN^{2/3}$.
--
--   **Formalization Note** The sequence $\kappa_N$ enters only through its value at $N$, so it is quantified as a number $\kappa\le C_\kappa N^{2/3}$ for each $N$. The constant depends on $C_\kappa$ and on a compact set $K$ of parameters $(\theta,\mu)$, and is chosen before the environment, $N$, $\kappa$, $m$, $n$. As on the page, $m,n\ge1$.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, eq. (4.32), proof of Theorem 2.1 (upper bound), p. 25; (4.9), p. 21

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem eq_4_32 (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hKpar : ∀ p ∈ K, 0 < p.1 ∧ p.1 < p.2)
    (Cκ : ℝ) :
    ∃ C : ℝ, ∀ θ μ : ℝ, (θ, μ) ∈ K →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (E : Env θ μ P) (N : ℝ), 1 ≤ N → ∀ κ : ℝ, κ ≤ Cκ * N ^ ((2 : ℝ) / 3) →
        ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → InRectK θ μ κ N m n →
        Eann E m n (fun x _ => (ξx x.1 : ℝ)) ≤ C * N ^ ((2 : ℝ) / 3) := by sorry

end LogGammaPolymer.Variance
