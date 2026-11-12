-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_informal_theorem_1_measurable_singletons
-- name    : MinimaxATE.Learnability.informal_theorem_1_measurable_singletons
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:17:50.200358+00:00
-- url     : https://prove2.me/theorems/29a1279f-4302-4583-8652-2ab91f8be777
-- title:
--   Informal Theorem 1 with measurable singletons (corrected: the σ-algebra must separate points)
-- statement:
--   **Source** (Informal Theorem 1, p. 3, with §3): for every measurable space $(X, \mathcal{A})$, $c \in (0, 1/2)$, $\mathcal{P} \subseteq [c, 1-c]^X$ and $\mathcal{M} \subseteq [0, 1]^X$, the ATE is learnable ($N_{\mathrm{ATE}}(\varepsilon, \delta; \mathcal{P}, \mathcal{M}, c) < \infty$ for all $\varepsilon, \delta \in (0, 1)$) iff $\mathrm{fat}^{\mathrm{mut}}_{\kappa,\gamma}(\mathcal{P}, \mathcal{M}) < \infty$ for all $\kappa, \gamma > 0$.
--
--   **Variant:** the same equivalence under the additional hypothesis that every singleton $\{x\}$ belongs to $\mathcal{A}$ (`MeasurableSingletonClass X`).
--
--   **Difference:** only that hypothesis; the trivial $\sigma$-algebra on $\mathbb{N}$ refutes the source's "only if" direction (evidence above). The "if" direction still inherits the measurability gap I5.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 3, Informal Theorem 1 (corrected)

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_SampleComplexity
import Definitions.Def_MinimaxATE_Learnability_FatDims

namespace MinimaxATE.Learnability

theorem informal_theorem_1_measurable_singletons {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1 / 2)
    (P M : Set (X → ℝ)) (hP : ∀ p ∈ P, ∀ x, p x ∈ Set.Icc c (1 - c))
    (hM : ∀ m ∈ M, ∀ x, m x ∈ Set.Icc (0 : ℝ) 1) :
    Learnable P M c ↔ ∀ κ γ : ℝ, 0 < κ → 0 < γ → mutFat P M κ γ < ⊤ := by sorry

end MinimaxATE.Learnability
