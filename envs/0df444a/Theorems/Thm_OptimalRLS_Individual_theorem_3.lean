-- Prove2me | Theorems.Thm_OptimalRLS_Individual_theorem_3
-- name    : OptimalRLS.Individual.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:55:47.143492+00:00
-- url     : https://prove2.me/theorems/e20c0314-1214-49e0-b64f-70e5473e5fb4
-- title:
--   Theorem 3, p. 11 — individual lower rate: for B > b, inf over algorithms of sup over P(b, c) of limsup E(excess risk)/ℓ^(−cB/(cB+1)) is positive
-- statement:
--   Assume Hypothesis 1 and $\dim Y = d < \infty$. Fix positive constants $M, \Sigma, R, \alpha, \beta$, and let $1 < b < \infty$ and $1 \le c \le 2$. Assume the prior $\mathcal P(b, c)$ of Definition 1 is nonempty.
--
--   Then for every $B > b$ the following individual lower rate holds:
--   $$\inf_{\{f_\ell\}_{\ell\in\mathbb N}}\ \sup_{\rho \in \mathcal P(b,c)}\ \limsup_{\ell \to +\infty} \frac{\mathbb E_{\mathbf z \sim \rho^\ell}\big(\mathcal E[f^\ell_{\mathbf z}] - \mathcal E[f_{\mathcal H}]\big)}{\ell^{-\frac{cB}{cB+1}}} > 0,$$
--   where the infimum is over all learning algorithms $\{f_\ell\}$, and $\mathcal E[f_{\mathcal H}] = \inf_{f \in \mathcal H}\mathcal E[f]$.
--
--   Equivalently, there is a constant $C > 0$ with the following property. For every learning algorithm there is a single distribution $\rho \in \mathcal P(b, c)$, which does not depend on the sample size, such that
--   $$\mathbb E_{\mathbf z \sim \rho^\ell}\big(\mathcal E[f^\ell_{\mathbf z}] - \inf_{\mathcal H}\mathcal E\big) \ \ge\ C\, \ell^{-\frac{cB}{cB+1}}$$
--   for infinitely many $\ell$.
--
--   Unlike a minimax lower rate, where the hard distribution may change with $\ell$, this shows that a fixed distribution in the prior is learned no faster than $\ell^{-cB/(cB+1)}$, for every $B > b$. The rate is arbitrarily close to the upper rate $\ell^{-bc/(bc+1)}$ that regularized least squares attains (Theorem 1).
--
--   **Formalization Note** The statement is the unfolding of the displayed inequality: "$\inf\sup\limsup > 0$" is equivalent to the existence of $C > 0$ such that every algorithm has some $\rho$ whose ratio exceeds $C$ for infinitely many $\ell$ ("for every $L$ there is $\ell \ge L$").
--   - A learning algorithm is a family of maps $f_\ell : Z^\ell \to \mathcal H$, with $Z^\ell$ encoded as `Fin ℓ → X × Y`.
--   - The expectation is a `lintegral` of the nonnegative excess risk under the product measure $\rho^\ell$.
--   - $\ell \ge 1$ is required because $\ell^{-cB/(cB+1)}$ is meaningless at $\ell = 0$.
--   - Two hypotheses are added. (i) $\mathcal P(b, c) \neq \emptyset$: the proof fixes "an arbitrary $\rho_0 \in \mathcal P(b, c)$", and with an empty prior the supremum is over the empty set and the statement fails. (ii) The algorithms are measurable, so that the expectation of the excess risk is meaningful; the infimum ranges over measurable algorithms.
--   - Positivity of $M, \Sigma, R, \alpha, \beta$ (Definition 1) is stated explicitly; $\kappa > 0$ is part of Hypothesis 1.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Theorem 3, p. 11; individual lower rate (3), p. 6; proof §5.4, pp. 25–30

import Mathlib
import Definitions.Def_OptimalRLS_Individual_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace OptimalRLS.Individual

variable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]

/-- **Theorem 3** (Caponnetto–De Vito 2007, p. 11). Assume `dim Y = d < +∞`, `1 < b < +∞` and
`1 ≤ c ≤ 2`. Then for every `B > b` the individual lower rate (3) holds with
`a_ℓ = ℓ^{−cB/(cB+1)}`:
`inf_{f_ℓ} sup_{ρ ∈ P(b,c)} limsup_ℓ E_{z∼ρ^ℓ}(E[f_z^ℓ] − E[f_H]) / ℓ^{−cB/(cB+1)} > 0`.

Unfolded: there is `C > 0` such that every (measurable) learning algorithm `est` has a single
`ρ ∈ P(b, c)` — not depending on `ℓ` — with `E_{z∼ρ^ℓ}(E[f_z^ℓ] − inf_H E) ≥ C ℓ^{−cB/(cB+1)}`
for infinitely many `ℓ ≥ 1`. The expectation is a `lintegral` of the nonnegative excess risk
under the product measure `ρ^ℓ` on samples `z : Fin ℓ → X × Y`.

Added hypotheses (disclosed): `P(b, c)` is nonempty (`hne`; the proof fixes "an arbitrary
`ρ₀ ∈ P(b, c)`", p. 26), and the algorithms are measurable (so that `E_z` is meaningful). -/
theorem theorem_3 {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 X H κ v)
    (M Sig R α β : ℝ) (hM : 0 < M) (hSig : 0 < Sig) (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (b c : ℝ) (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hne : ∃ ρ₀ : Measure (X × Y), InPrior (H := H) M Sig R α β b c ρ₀)
    (B : ℝ) (hB : b < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ est : (ℓ : ℕ) → (Fin ℓ → X × Y) → H, (∀ ℓ, Measurable (est ℓ)) →
      ∃ ρ : Measure (X × Y), InPrior (H := H) M Sig R α β b c ρ ∧
        ∀ L : ℕ, ∃ ℓ : ℕ, L ≤ ℓ ∧ 1 ≤ ℓ ∧
          ENNReal.ofReal (C * (ℓ : ℝ) ^ (-(c * B / (c * B + 1))))
            ≤ ∫⁻ z, ENNReal.ofReal (risk ρ (est ℓ z) - ⨅ f : H, risk ρ f)
                ∂(Measure.pi fun _ : Fin ℓ => ρ) := by sorry

end OptimalRLS.Individual
