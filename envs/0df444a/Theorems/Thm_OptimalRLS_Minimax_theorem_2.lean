-- Prove2me | Theorems.Thm_OptimalRLS_Minimax_theorem_2
-- name    : OptimalRLS.Minimax.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:31:36.161308+00:00
-- url     : https://prove2.me/theorems/5a62666b-3762-4f21-8f97-94ba0bc5df89
-- title:
--   Theorem 2, p. 11 — minimax lower rate: lim_{τ→0} liminf_ℓ inf_{f_ℓ} sup_{ρ∈P(b,c)} P[E[f_z^ℓ] − E[f_H] > τℓ^(−bc/(bc+1))] = 1
-- statement:
--   Let $X$ be a Polish space, $Y$ a real Hilbert space of finite dimension $d$, and $\mathcal H$ a separable Hilbert space of functions $X \to Y$ satisfying Hypothesis 1 with constant $\kappa$. Fix positive constants $M, \Sigma, R, \alpha, \beta$, and $1 < b < +\infty$, $1 \le c \le 2$, and assume the prior $\mathcal P(b,c)$ of Definition 1 is nonempty. For a probability measure $\rho$ on $Z = X \times Y$ write $\mathcal E[f] = \int \|f(x) - y\|^2 d\rho$ and $\mathcal E[f_{\mathcal H}] = \inf_{f \in \mathcal H} \mathcal E[f]$. Then
--   $$\lim_{\tau \to 0}\ \liminf_{\ell \to +\infty}\ \inf_{f_\ell}\ \sup_{\rho \in \mathcal P(b,c)}\ \mathbb P_{\mathbf z \sim \rho^\ell}\Big[\mathcal E[f^\ell_{\mathbf z}] - \mathcal E[f_{\mathcal H}] > \tau\, \ell^{-\frac{bc}{bc+1}}\Big] = 1,$$
--   where the infimum runs over all learning algorithms $f_\ell : Z^\ell \to \mathcal H$.
--
--   Equivalently, since probabilities are at most $1$: for every $\varepsilon > 0$ there is $\tau_0 > 0$ such that for every $0 < \tau \le \tau_0$ there is $L$ such that for every $\ell \ge L$ and every algorithm $f_\ell$ some $\rho \in \mathcal P(b,c)$ (which may depend on $f_\ell$, $\ell$ and $\tau$) satisfies
--   $$\mathbb P_{\mathbf z \sim \rho^\ell}\Big[\mathcal E[f^\ell_{\mathbf z}] - \mathcal E[f_{\mathcal H}] > \tau\, \ell^{-\frac{bc}{bc+1}}\Big] \ge 1 - \varepsilon .$$
--
--   Together with Theorem 1 this shows that regularized least squares with a suitable regularization parameter attains the optimal rate $\ell^{-bc/(bc+1)}$ over $\mathcal P(b,c)$ when $Y$ is finite dimensional and $1 < c \le 2$, and is optimal up to a logarithmic factor for $c = 1$.
--
--   **Formalization Note.** The statement is the $\varepsilon$–$\tau$–$L$ unfolding of the limit displayed above. Three hypotheses implicit on the page are explicit: (i) $\mathcal P(b,c)$ is nonempty — the proof fixes some $\rho_0 \in \mathcal P(b,c)$, and over an empty prior the supremum is over the empty set and the statement fails; (ii) the algorithms are measurable maps $Z^\ell \to \mathcal H$, the reading under which the probability is defined (this restricts the infimum relative to "all mappings"); (iii) the constants $M, \Sigma, R, \alpha, \beta, \kappa$ are positive. The event is measured by the product measure $\rho^{\otimes \ell}$. $\mathcal P(b,c)$ is `InPrior` (Definition 1 with $N = +\infty$); the eigenvalues are indexed from $0$ in Lean.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Theorem 2, p. 11; minimax lower rate (2), p. 5; proof §5.3, pp. 20–25 (Proof of Th. 2, p. 25)

import Mathlib
import Definitions.Def_OptimalRLS_Minimax_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace OptimalRLS.Minimax

/-- **Theorem 2** (minimax lower rate), Caponnetto & De Vito (2007), p. 11. Assume `dim Y = d < +∞`,
Hypothesis 1 with `κ`, positive constants `M, Σ (Sig), R, α, β`, `1 < b < +∞`, `1 ≤ c ≤ 2`, and that
`P(b, c)` is nonempty. Then
`lim_{τ→0} liminf_{ℓ→∞} inf_{f_ℓ} sup_{ρ∈P(b,c)} P_{z∼ρ^ℓ}[E[f_z^ℓ] − E[f_H] > τ ℓ^{−bc/(bc+1)}] = 1`,
the infimum over (measurable) maps `f_ℓ : Z^ℓ → H`, `E[f_H] = inf_{f∈H} E[f]`. Since probabilities are at
most `1`, this is: for every `ε > 0` there is `τ₀ > 0` such that for every `0 < τ ≤ τ₀`, for all large
`ℓ`, every algorithm `f_ℓ` admits some `ρ ∈ P(b, c)` (depending on `f_ℓ`, `ℓ` and `τ`) with
`P[…] ≥ 1 − ε`. -/
theorem theorem_2
    {X Y H : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]
    {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 H κ v)
    (M Sig R α β b c : ℝ) (hM : 0 < M) (hSig : 0 < Sig) (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hne : ∃ ρ₀ : Measure (X × Y), ∃ _ : IsProbabilityMeasure ρ₀,
      InPrior H M Sig R α β b c ρ₀) :
    ∀ ε : ℝ, 0 < ε → ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → ∃ L : ℕ, ∀ ℓ : ℕ, L ≤ ℓ →
      ∀ est : (Fin ℓ → X × Y) → H, Measurable est →
        ∃ ρ : Measure (X × Y), ∃ _ : IsProbabilityMeasure ρ,
          InPrior H M Sig R α β b c ρ ∧
          ENNReal.ofReal (1 - ε) ≤ (Measure.pi fun _ : Fin ℓ => ρ)
            {z | τ * (ℓ : ℝ) ^ (-(b * c / (b * c + 1))) <
              risk ρ (est z) - ⨅ f : H, risk ρ f} := by sorry

end OptimalRLS.Minimax
