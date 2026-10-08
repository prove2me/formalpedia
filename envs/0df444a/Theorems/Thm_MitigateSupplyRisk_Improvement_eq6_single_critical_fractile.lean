-- Prove2me | Theorems.Thm_MitigateSupplyRisk_Improvement_eq6_single_critical_fractile
-- name    : MitigateSupplyRisk.Improvement.eq6_single_critical_fractile
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:50.936605+00:00
-- url     : https://prove2.me/theorems/1f00b0b6-163b-4fe5-bf69-7079e3970f18
-- title:
--   §4.1, Eq. (6), p. 494 (single-supplier instance, η = 0) — the critical fractile F⁻¹(φ) is an optimal order for every reliability index
-- statement:
--   Consider the single-supplier model with no committed cost, $\eta = 0$, so that $\varphi = (r+p-c)/(r+p-v)$, and assume $0 < \varphi < 1$ (that is, $v < c < r+p$). Let
--   $$\hat q = \inf\{t \in \mathbb R : F(t) \ge \varphi\}$$
--   be the critical fractile of demand. Then:
--   1. $\hat q \ge 0$;
--   2. for every reliability index $a$, $\hat q$ maximizes $\Pi_2(\cdot\,; a)$ over $q \ge 0$:
--   $$\Pi_2(q; a) \le \Pi_2(\hat q; a) \qquad \text{for all } q \ge 0;$$
--   3. if demand has no atoms, $F(\hat q) = \varphi$;
--   4. if demand has no atoms, every optimal order $q^* > 0$ (a maximizer of $\Pi_2(\cdot\,; a)$ over $q \ge 0$) satisfies the interior optimality condition
--   $$G(K - q^*, a)\,(\varphi - F(q^*)) = 0 .$$
--
--   Item 4 is the single-supplier, $\eta = 0$ case of the paper's interior optimality condition (6), $\psi + G(K - q^*, a)(\varphi - F(q^*)) = 0$ (here $\psi = 0$ and the other supplier delivers $y_j = 0$); items 1–3 say it is solved by the critical fractile, $F(q^*) = \varphi$. In particular, the optimal order quantity does not depend on the reliability index, which is what makes the first-stage profit tractable in Theorem 3.
--
--   **Formalization Note** The paper states (6) for two suppliers and applies it to single sourcing by giving the other supplier an infinite cost (p. 496). The Lean statement is the single-supplier instance, stated as optimality of $\hat q$ rather than as the derivative identity, so it needs no density of demand. The bounds $0 < \varphi < 1$ make the infimum that of a nonempty set bounded below; they are the paper's implicit reading ($v < c < r+p$) of an interior solution.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 494 (PDF 6), §4.1, Eq. (6); p. 496 (PDF 8), §4.2.1 (single sourcing as a special case of §4.1)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Improvement_Model

open MeasureTheory ProbabilityTheory Set

namespace MitigateSupplyRisk.Improvement

theorem eq6_single_critical_fractile (M : Model) (hM : M.Assumptions) (hη : M.η = 0)
    (hφ₀ : 0 < M.φ) (hφ₁ : M.φ < 1) :
    0 ≤ sInf {t : ℝ | M.φ ≤ M.F t} ∧
    (∀ a : ℝ, IsMaxOn (fun q => M.Pi2 q a) (Ici 0) (sInf {t : ℝ | M.φ ≤ M.F t})) ∧
    (NullSingletonClass M.μ → M.F (sInf {t : ℝ | M.φ ≤ M.F t}) = M.φ) ∧
    (∀ a qStar : ℝ, 0 < qStar → IsMaxOn (fun q => M.Pi2 q a) (Ici 0) qStar →
      NullSingletonClass M.μ → M.G (M.K - qStar) a * (M.φ - M.F qStar) = 0) := by sorry

end MitigateSupplyRisk.Improvement
