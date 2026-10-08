-- Prove2me | Theorems.Thm_MitigateSupplyRisk_Heterogeneity_lemma_5
-- name    : MitigateSupplyRisk.Heterogeneity.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:42.940659+00:00
-- url     : https://prove2.me/theorems/2980919e-7bd6-4f92-956a-d456593ea3e4
-- title:
--   Lemma 5, p. 504 — the combined-strategy profit Π₁(a) of (5) is submodular in the reliability indices a
-- statement:
--   Consider the two-supplier model with arbitrary (not necessarily identical) suppliers satisfying the standing assumptions, and let $\Pi_1(a)$ be the first-stage expected profit (5) of the combined strategy, in which the firm improves one or both suppliers to target indices $a = (a_1, a_2)$ and then dual sources:
--   $$\Pi_1(a) = \sum_{i=1}^2 -m_i z_i(a_i) + \theta_1\theta_2 \Pi_2^*(a_1,a_2) + \theta_1(1-\theta_2)\Pi_2^*(a_1,a_2^0) + (1-\theta_1)\theta_2\Pi_2^*(a_1^0,a_2) + (1-\theta_1)(1-\theta_2)\Pi_2^*(a_1^0,a_2^0).$$
--   Then $\Pi_1$ is submodular on $[a_1^0, \infty) \times [a_2^0, \infty)$: for all $a, b$ in this set,
--   $$\Pi_1(a \vee b) + \Pi_1(a \wedge b) \le \Pi_1(a) + \Pi_1(b).$$
--   where $\vee$ and $\wedge$ are the componentwise maximum and minimum.
--
--   Submodularity says that improving one supplier is worth less when the other supplier is more reliable: the two improvement efforts are substitutes. The paper adds that $\Pi_1$ is not in general jointly concave.
--
--   **Formalization Note** The domain $a_i \ge a_i^0$ is the set of reachable target indices. The standing assumptions are the fields of `Model.Standing`, including the disclosed readings $r, p, c_i \ge 0$ and $v < r + p$.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 504 (PDF 16), §6, Lemma 5; Eq. (5), p. 493 (PDF 5)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Heterogeneity_Model

namespace MitigateSupplyRisk.Heterogeneity
theorem lemma_5 (M : Model) (hM : M.Standing) (a b : Fin 2 → ℝ)
    (ha : ∀ i, M.a0 i ≤ a i) (hb : ∀ i, M.a0 i ≤ b i) :
    M.Pi1 (a ⊔ b) + M.Pi1 (a ⊓ b) ≤ M.Pi1 a + M.Pi1 b := by sorry
end MitigateSupplyRisk.Heterogeneity
