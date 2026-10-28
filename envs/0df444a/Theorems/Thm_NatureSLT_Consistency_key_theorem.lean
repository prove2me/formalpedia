-- Prove2me | Theorems.Thm_NatureSLT_Consistency_key_theorem
-- name    : NatureSLT.Consistency.key_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:34.233329+00:00
-- url     : https://prove2.me/theorems/0a9a6294-99b2-48e0-afc4-0f019b5bebad
-- title:
--   Theorem 2.1 — the key theorem: ERM is consistent iff uniform one-sided convergence holds
-- statement:
--   Let $F$ be a probability measure on $Z$ and let $Q(z,\alpha)$, $\alpha\in\Lambda$, be a set of $F$-integrable real functions whose risks are bounded:
--
--   $$A \le \int Q(z,\alpha)\,dF(z) \le B \qquad (A\le R(\alpha)\le B) \quad\text{for all } \alpha\in\Lambda.$$
--
--   Write $R_{\mathrm{emp}}(\alpha)=\frac1\ell\sum_{i=1}^\ell Q(z_i,\alpha)$ for the empirical risk on an i.i.d. sample $z_1,\dots,z_\ell$ from $F$. Then the ERM principle is (nontrivially) consistent — for every $c$ with $\Lambda(c)=\{\alpha : R(\alpha)>c\}$ nonempty, $\inf_{\Lambda(c)}R_{\mathrm{emp}}\to\inf_{\Lambda(c)}R$ in probability — if and only if the empirical risk converges uniformly to the actual risk in the one-sided sense
--
--   $$\lim_{\ell\to\infty}P\Bigl\{\sup_{\alpha\in\Lambda}\bigl(R(\alpha)-R_{\mathrm{emp}}(\alpha)\bigr)>\varepsilon\Bigr\}=0\qquad\forall\varepsilon>0. \tag{2.4}$$
--
--   This is the key theorem of learning theory (Vapnik and Chervonenkis, 1989): consistency of empirical risk minimization is determined by the worst function of the set, so any analysis of the ERM principle must be a worst-case analysis.
--
--   **Formalization Note** Integrability of each $Q(\cdot,\alpha)$ is assumed so that $R(\alpha)$ is the book's integral. The book takes probabilities of the events $\{\sup_\alpha(R-R_{\mathrm{emp}})>\varepsilon\}$ and $\{|\inf_{\Lambda(c)}R_{\mathrm{emp}}-\inf_{\Lambda(c)}R|>\varepsilon\}$ without comment; the theorem assumes, for every $\ell$ and $c$, that $\sup_\alpha(R(\alpha)-R_{\mathrm{emp}}(\alpha))$ and $\inf_{\alpha\in\Lambda(c)}R_{\mathrm{emp}}(\alpha)$ are measurable functions of the sample. Suprema and the empirical infimum are taken in the extended reals; probabilities are values of the product measure $F^\ell$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 38, Theorem 2.1, Eqs. (2.3), (2.4)

import Mathlib
import Definitions.Def_NatureSLT_Consistency_risk
import Definitions.Def_NatureSLT_Consistency_nontriviallyConsistent
import Definitions.Def_NatureSLT_Consistency_uniformConvergence

open MeasureTheory Filter Topology

namespace NatureSLT.Consistency

/-- **Theorem 2.1** (the key theorem of learning theory; Vapnik 2000, p. 38). Let `Q(z, α)`,
`α ∈ Λ`, be a set of functions with `A ≤ ∫ Q(z, α) dF(z) ≤ B` for all `α`. Then the ERM principle
is (nontrivially) consistent iff the empirical risk converges uniformly one-sidedly to the risk,
`lim_{ℓ→∞} P{sup_{α ∈ Λ} (R(α) − R_emp(α)) > ε} = 0` for all `ε > 0` (2.4).
`hint`: each `Q(·, α)` is integrable, so that `R(α)` is the book's integral. `hsup`, `hinf`: the
book's tacit measurability — the sample functions `sup_α (R(α) − R_emp(α))` and
`inf_{α ∈ Λ(c)} R_emp(α)` whose probabilities are taken are measurable. -/
theorem key_theorem {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (hint : ∀ α, Integrable (Q α) F) (A B : ℝ)
    (hAB : ∀ α, A ≤ risk F Q α ∧ risk F Q α ≤ B)
    (hsup : ∀ ℓ : ℕ, Measurable (fun z : Fin ℓ → Z => supOneSidedDeviation F Q z))
    (hinf : ∀ (c : ℝ) (ℓ : ℕ),
      Measurable (fun z : Fin ℓ → Z => infEmpiricalRisk Q (levelSet F Q c) z)) :
    NontriviallyConsistent F Q ↔ UniformOneSidedConvergence F Q := by sorry

end NatureSLT.Consistency
