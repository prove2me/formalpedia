-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_proposition_5_3
-- name    : LogGammaPolymer.Variance.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:11.242003+00:00
-- url     : https://prove2.me/theorems/ff49c2e9-086a-4250-a56f-ac5197e9ca20
-- title:
--   Proposition 5.3 — lim_{δ↘0} limsup_N P{1 ≤ ξ_x ≤ δN^{2/3}} = 0, and the same for ξ_y
-- statement:
--   Assume (2.4) and rectangle dimensions (2.6). Then
--   $$\lim_{\delta\searrow0}\ \varlimsup_{N\to\infty}\ P\{1\le\xi_x\le\delta N^{2/3}\}=0,$$
--   where $P=P_{m,n}$ is the annealed polymer measure. The same result holds for $\xi_y$.
--
--   Under the annealed measure the path does not exit an axis at a distance $o(N^{2/3})$ from the origin with non-vanishing probability. Combined with (3.18)–(3.19) this yields the lower variance bound, Corollary 5.6.
--
--   **Formalization Note** Stated as: for every $\varepsilon>0$ there are $\delta>0$ and $N_0$ such that $P_{m,n}\{1\le\xi_x\le\delta N^{2/3}\}\le\varepsilon$ and $P_{m,n}\{1\le\xi_y\le\delta N^{2/3}\}\le\varepsilon$ for every environment satisfying (2.4), every $N\ge N_0$ and every $(m,n)$ satisfying (2.6). The probabilities are nondecreasing in $\delta$, so this is the printed double limit. $\gamma$ is an arbitrary real: for $\gamma<0$ condition (2.6) is empty.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Proposition 5.3, p. 27

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem proposition_5_3 {θ μ : ℝ} (hθ : 0 < θ) (hθμ : θ < μ) (γ : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℝ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (E : Env θ μ P) (N : ℝ), N₀ ≤ N → ∀ m n : ℕ, InRect θ μ γ N m n →
        Pann E m n (fun x => 1 ≤ ξx x.1 ∧ (ξx x.1 : ℝ) ≤ δ * N ^ ((2 : ℝ) / 3)) ≤ ε ∧
        Pann E m n (fun x => 1 ≤ ξy x.1 ∧ (ξy x.1 : ℝ) ≤ δ * N ^ ((2 : ℝ) / 3)) ≤ ε := by sorry

end LogGammaPolymer.Variance
