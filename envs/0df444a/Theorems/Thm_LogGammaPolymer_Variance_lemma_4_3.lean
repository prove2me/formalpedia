-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_lemma_4_3
-- name    : LogGammaPolymer.Variance.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:02.82939+00:00
-- url     : https://prove2.me/theorems/de6d0288-af06-4d10-9f24-0ace4dd2474f
-- title:
--   Lemma 4.3 — tail bounds (4.34)–(4.35) for the quenched exit-point probabilities Q^ω{ξ_x ≥ u}, Q^ω{ξ_y ≥ u}
-- statement:
--   Assume (2.4) and rectangle dimensions (4.9) with $\kappa_N\le C_\kappa N^{2/3}$. There are finite positive constants $\delta,\delta_1,c,c_1$ and $C$ such that for $N\ge1$ and $(1\vee c\kappa_N)\le u\le\delta N$,
--   $$\mathbb P\bigl[Q^\omega\{\xi_x\ge u\}\ge e^{-\delta u^2/N}\bigr]\le C\Bigl(\frac{N^{8/3}}{u^4}+\frac{N^2}{u^3}\Bigr)\qquad(4.34)$$
--   while for $N\ge1$ and $u\ge(1\vee c\kappa_N\vee\delta N)$,
--   $$\mathbb P\bigl[Q^\omega\{\xi_x\ge u\}\ge e^{-\delta_1u}\bigr]\le e^{-c_1u}\qquad(4.35).$$
--   The same bounds hold for $\xi_y$, and the same constants work for $0<\theta<\mu$ that vary in a compact set.
--
--   Here $\mathbb P$ is the probability of the environment and $Q^\omega=Q^\omega_{m,n}$ the quenched polymer measure. The lemma controls the exit point of the path from the axes at the scale $N^{2/3}$, uniformly in the environment except on events of small probability.
--
--   **Formalization Note** $u$ is real and $\xi_x\ge u$ compares the natural number $\xi_x$ cast to $\mathbb R$. $\kappa_N$ is quantified as a number $\kappa\le C_\kappa N^{2/3}$ for each $N$, and $(m,n)\in\mathbb N^2$. The constants depend on $C_\kappa$ and on a compact set $K$ of parameters $(\theta,\mu)$, and are chosen before the environment and $N$.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Lemma 4.3, (4.34)–(4.35), p. 25

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem lemma_4_3 (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hKpar : ∀ p ∈ K, 0 < p.1 ∧ p.1 < p.2)
    (Cκ : ℝ) :
    ∃ δ δ₁ c c₁ C : ℝ, 0 < δ ∧ 0 < δ₁ ∧ 0 < c ∧ 0 < c₁ ∧ 0 < C ∧
      ∀ θ μ : ℝ, (θ, μ) ∈ K →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (E : Env θ μ P) (N : ℝ), 1 ≤ N → ∀ κ : ℝ, κ ≤ Cκ * N ^ ((2 : ℝ) / 3) →
        ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → InRectK θ μ κ N m n →
        (∀ u : ℝ, max 1 (c * κ) ≤ u → u ≤ δ * N →
          P.real {ω | Real.exp (-(δ * u ^ 2 / N)) ≤
              Q (E.conf ω) m n (fun x => u ≤ (ξx x.1 : ℝ))} ≤
            C * (N ^ ((8 : ℝ) / 3) / u ^ 4 + N ^ 2 / u ^ 3)) ∧
        (∀ u : ℝ, max 1 (max (c * κ) (δ * N)) ≤ u →
          P.real {ω | Real.exp (-(δ₁ * u)) ≤ Q (E.conf ω) m n (fun x => u ≤ (ξx x.1 : ℝ))} ≤
            Real.exp (-(c₁ * u))) ∧
        (∀ u : ℝ, max 1 (c * κ) ≤ u → u ≤ δ * N →
          P.real {ω | Real.exp (-(δ * u ^ 2 / N)) ≤
              Q (E.conf ω) m n (fun x => u ≤ (ξy x.1 : ℝ))} ≤
            C * (N ^ ((8 : ℝ) / 3) / u ^ 4 + N ^ 2 / u ^ 3)) ∧
        (∀ u : ℝ, max 1 (max (c * κ) (δ * N)) ≤ u →
          P.real {ω | Real.exp (-(δ₁ * u)) ≤ Q (E.conf ω) m n (fun x => u ≤ (ξy x.1 : ℝ))} ≤
            Real.exp (-(c₁ * u))) := by sorry

end LogGammaPolymer.Variance
