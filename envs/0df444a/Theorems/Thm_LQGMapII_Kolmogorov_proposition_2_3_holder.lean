-- Prove2me | Theorems.Thm_LQGMapII_Kolmogorov_proposition_2_3_holder
-- name    : LQGMapII.Kolmogorov.proposition_2_3_holder
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:24.153474+00:00
-- url     : https://prove2.me/theorems/b5945a25-119a-4ccd-97d6-f7eeac2d92e7
-- title:
--   Proposition 2.3 (2.7), p. 30 — a modification that is γ-Hölder for every γ ∈ (0, β/α)
-- statement:
--   Let $(X_u)_{u \in [0,1]^d}$ be a real random field on a probability space $(\Omega, \mathcal F, \mathbf P)$, and let $\alpha, \beta, c_0 > 0$ be constants such that for all $u, v \in [0,1]^d$
--   $$
--   \mathbf E\big[|X_u - X_v|^\alpha\big] \le c_0 |u - v|^{d+\beta}. \qquad (2.6)
--   $$
--   Then there is a modification $Y$ of $X$ (that is, $Y_u = X_u$ almost surely for every $u$) such that for every $\gamma \in (0, \beta/\alpha)$ and every $\omega \in \Omega$ there is $M > 0$ with
--   $$
--   |Y_u(\omega) - Y_v(\omega)| \le M\, |u - v|^\gamma \quad \text{for all } u, v \in [0,1]^d. \qquad (2.7)
--   $$
--
--   This is the classical Kolmogorov–Čentsov continuity criterion on the cube, the first statement of Proposition 2.3. One modification works for all exponents $\gamma$ simultaneously; the Hölder constant $M$ depends on $\omega$ and $\gamma$.
--
--   **Formalization Note** (2.6) is `IsKolmogorovProcess X P α (d + β) c₀`: the lower Lebesgue integral of $|X_u - X_v|^\alpha$ in $[0,\infty]$ is at most $c_0 |u - v|^{d+\beta}$, and each pair $(X_u, X_v)$ is Borel measurable (the paper's "random field"). $|u - v|$ is the Euclidean distance. The Hölder bound is stated for every $\omega$, as the paper states it for the modification itself (changing $Y$ on a null set keeps it a modification). Mathlib's `HolderWith M γ` takes $M$ and $\gamma$ as nonnegative reals.
-- source:
--   Miller, Sheffield, Liouville quantum gravity and the Brownian map II, Ann. Probab. (2021), DOI 10.1214/21-AOP1506, accepted manuscript, Proposition 2.3, (2.6)–(2.7), p. 30

import Mathlib
import Definitions.Def_LQGMapII_Kolmogorov_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMapII.Kolmogorov

/-- Proposition 2.3, first statement (2.7), p. 30: under (2.6) the field has a modification that
is `γ`-Hölder for every `γ ∈ (0, β/α)`, with a (random) constant `M > 0`. -/
theorem proposition_2_3_holder {d : ℕ} {α β : ℝ} {c₀ : ℝ≥0} (hα : 0 < α) (hβ : 0 < β)
    (hc₀ : 0 < c₀) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Cube d → Ω → ℝ) (hX : IsKolmogorovProcess X P α ((d : ℝ) + β) c₀) :
    ∃ Y : Cube d → Ω → ℝ, (∀ u, Y u =ᵐ[P] X u) ∧
      ∀ γ : ℝ≥0, 0 < γ → (γ : ℝ) < β / α →
        ∀ ω, ∃ M : ℝ≥0, 0 < M ∧ HolderWith M γ (fun u ↦ Y u ω) := by sorry

end LQGMapII.Kolmogorov
