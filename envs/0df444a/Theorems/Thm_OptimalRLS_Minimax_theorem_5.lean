-- Prove2me | Theorems.Thm_OptimalRLS_Minimax_theorem_5
-- name    : OptimalRLS.Minimax.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:31:38.02617+00:00
-- url     : https://prove2.me/theorems/6c661c8f-cb60-45eb-ac1e-2c09d96e64c4
-- title:
--   Theorem 5, p. 24 — for every algorithm some ρ_* ∈ P(b, c) has P[excess risk > ε/4] ≥ min{N*/(N*+1), η̄√N* e^(−4ℓε/(15dκ^cR))}
-- statement:
--   Work in the setting of §5.3: $\dim Y = d < \infty$, Hypothesis 1 with constant $\kappa$, positive constants $M, \Sigma, R, \alpha, \beta$, $1 < b$, $1 \le c \le 2$, and $\nu$ the marginal of some $\rho_0 \in \mathcal P(b,c)$, i.e. a probability measure on $X$ whose operator $T = \sum_{n\ge1} t_n \langle\cdot,e_n\rangle e_n$ has decreasing eigenvalues with $\alpha \le n^b t_n \le \beta$. Assume
--   $$\min(M, \Sigma) \ge 2(4d+1)\sqrt{\kappa^c R} \qquad (53).$$
--   Then there are constants $\gamma > 0$ and $\epsilon_0 > 0$ such that for every $0 < \epsilon \le \epsilon_0$, every sample size $\ell \in \mathbb N$ and every learning algorithm $\mathbf z \mapsto f^\ell_{\mathbf z} \in \mathcal H$ on $Z^\ell$, there is a distribution $\rho_* \in \mathcal P(b,c)$ whose regression function $f_{\rho_*}$ belongs to $\mathcal H$ and
--   $$\mathbb P_{\mathbf z \sim \rho_*^\ell}\Big[\mathcal E_{\rho_*}[f^\ell_{\mathbf z}] - \mathcal E_{\rho_*}[f_{\rho_*}] > \frac{\epsilon}{4}\Big] \ge \min\Big\{ \frac{N^*_\epsilon}{N^*_\epsilon + 1},\ \bar\eta \sqrt{N^*_\epsilon}\, e^{-\frac{4\ell\epsilon}{15 d \kappa^c R}} \Big\},$$
--   where $N^*_\epsilon = e^{\gamma \epsilon^{-1/(bc)}}$ and $\bar\eta = e^{-3/e}$.
--
--   This is a restatement, in the present setting, of the general minimax lower bound of DeVore, Kerkyacharian, Picard and Temlyakov; Theorem 2 follows from it by choosing $\epsilon$ proportional to $\ell^{-bc/(bc+1)}$.
--
--   **Formalization Note.** The constants $\gamma, \epsilon_0$ are those of Proposition 5; as a standalone statement they are existential, chosen before $\epsilon$, $\ell$ and the algorithm. The algorithm is assumed measurable, the reading under which the probability on the left is defined (the event is measured by the product measure $\rho_*^{\otimes \ell}$). The distribution $\rho_*$ may depend on the algorithm, on $\ell$ and on $\epsilon$. The regression function is expressed through the conditional distribution: $\int_Y y\, d\rho_*(y\mid x) = f_{\rho_*}(x)$ for $\rho_{*,X}$-almost every $x$. The proof uses Lemma 3.3 and Eq. 3.12 of DeVore et al., which are not stated in this paper.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Theorem 5, p. 24; proof pp. 24–25 (using Lemma 3.3 and Eq. 3.12 of DeVore et al. [10])

import Mathlib
import Definitions.Def_OptimalRLS_Minimax_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace OptimalRLS.Minimax

/-- **Theorem 5**, Caponnetto & De Vito (2007), p. 24. In the setting of §5.3 (`dim Y = d < +∞`,
Hypothesis 1 with `κ`, constants `M, Σ (Sig), R, α, β > 0`, `1 < b`, `1 ≤ c ≤ 2`, and `ν` the marginal
of some `ρ₀ ∈ P(b, c)`, i.e. a probability measure with the spectral decomposition (52) satisfying
(17)), assume (53) `min(M, Σ) ≥ 2(4d + 1)√(κ^c R)`. There are `γ > 0` and `ε₀ > 0` (those of
Proposition 5) such that for every `0 < ε ≤ ε₀`, every `ℓ` and every (measurable) learning algorithm
`z ↦ f_z^ℓ ∈ H` on `Z^ℓ`, some `ρ_* ∈ P(b, c)` with regression function `f_{ρ_*} ∈ H` satisfies
`P_{z∼ρ_*^ℓ}[E_{ρ_*}[f_z^ℓ] − E_{ρ_*}[f_{ρ_*}] > ε/4] ≥ min{N*/(N* + 1), η̄ √N* e^{−4ℓε/(15dκ^cR)}}`
with `N* = e^{γ ε^{−1/(bc)}}` and `η̄ = e^{−3/e}`. -/
theorem theorem_5
    {X Y H : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]
    {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 H κ v)
    (M Sig R α β b c : ℝ) (hM : 0 < M) (hSig : 0 < Sig) (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (ν : Measure X) [IsProbabilityMeasure ν] (e : ℕ → H) (t : ℕ → ℝ)
    (heig : IsEigenSystem ν e t) (hanti : Antitone t)
    (h17 : ∀ n : ℕ, α ≤ ((n : ℝ) + 1) ^ b * t n ∧ ((n : ℝ) + 1) ^ b * t n ≤ β)
    (h53 : 2 * (4 * (Module.finrank ℝ Y : ℝ) + 1) * Real.sqrt (κ ^ c * R) ≤ min M Sig) :
    ∃ γ ε₀ : ℝ, 0 < γ ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ ℓ : ℕ,
      ∀ est : (Fin ℓ → X × Y) → H, Measurable est →
        ∃ ρ : Measure (X × Y), ∃ _ : IsProbabilityMeasure ρ, ∃ fstar : H,
          InPrior H M Sig R α β b c ρ ∧
          (∀ᵐ x ∂ρ.fst, ∫ y, y ∂(ρ.condKernel x) = fstar x) ∧
          ENNReal.ofReal
              (min (Real.exp (γ * ε ^ (-(1 / (b * c)))) / (Real.exp (γ * ε ^ (-(1 / (b * c)))) + 1))
                (Real.exp (-3 / Real.exp 1) * Real.sqrt (Real.exp (γ * ε ^ (-(1 / (b * c))))) *
                  Real.exp (-(4 * (ℓ : ℝ) * ε /
                    (15 * (Module.finrank ℝ Y : ℝ) * κ ^ c * R)))))
            ≤ (Measure.pi fun _ : Fin ℓ => ρ) {z | ε / 4 < risk ρ (est z) - risk ρ fstar} := by sorry

end OptimalRLS.Minimax
