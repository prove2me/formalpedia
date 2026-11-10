-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_informal_theorem_1
-- name    : MinimaxATE.Learnability.informal_theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:01:57.23224+00:00
-- url     : https://prove2.me/theorems/696181a0-3c60-4846-9628-f600bdc3aca0
-- title:
--   Informal Theorem 1 (main result) — the ATE is learnable iff $\mathrm{fat}^{\mathrm{mut}}_{\kappa,\gamma}(\mathcal P,\mathcal M)<\infty$ at every scale
-- statement:
--   Let $(\mathcal X,\mathcal A)$ be any measurable space of covariates, $c\in(0,1/2)$ an overlap parameter, and $\mathcal P\subseteq[c,1-c]^{\mathcal X}$, $\mathcal M\subseteq[0,1]^{\mathcal X}$ arbitrary classes of propensity scores and outcome regressions. Then the average treatment effect is learnable from samples of an observational study in $\mathcal D(\mathcal P,\mathcal M,c)$ — that is, $N_{\mathrm{ATE}}(\varepsilon,\delta;\mathcal P,\mathcal M,c)<\infty$ for every $\varepsilon,\delta\in(0,1)$ — if and only if the mutual fat-shattering dimension is finite at every pair of scales:
--   $$\Big(\forall\,\varepsilon,\delta\in(0,1):\ N_{\mathrm{ATE}}(\varepsilon,\delta;\mathcal P,\mathcal M,c)<\infty\Big)\iff\Big(\forall\,\kappa,\gamma>0:\ \mathrm{fat}^{\mathrm{mut}}_{\kappa,\gamma}(\mathcal P,\mathcal M)<\infty\Big).$$
--
--   This is the paper's headline result: a combinatorial characterization of when the ATE can be estimated to any accuracy with finitely many samples, uniformly over the realizable studies, in terms of the joint complexity of the two nuisance classes rather than either class alone. The paper proves "if" from Theorem 1.8 and "only if" from Theorem 5.10.
--
--   **Formalization Note.** Studies, unconfoundedness, overlap, realizability, randomized measurable estimators and $N_{\mathrm{ATE}}$ are those of the mission's definitions. No condition is placed on the $\sigma$-algebra and no measurability is required of the members of $\mathcal P$, $\mathcal M$, exactly as in the paper; with these conventions the "only if" direction is false over a $\sigma$-algebra that does not separate points (see the mission's findings). The statement is posed as printed.
--
--   Differences from the source:
--   - reading: "fat^mut(P, M) < ∞" → fat^mut_{κ,γ}(P, M) < ∞ for every κ, γ > 0; reason: footnote 2 (p. 3) and the abstract ("finite mutual fat-shattering dimension at any scale").
--   - reading: "ATE is learnable" → N_ATE(ε, δ; P, M, c) < ∞ for every ε, δ ∈ (0, 1), with N_ATE of eq. (1); reason: Problem 1 (p. 2) and eq. (1) (p. 19).
--   - reading: classes P, M ⊆ [0, 1]^X of Problem 1 → P ⊆ [c, 1−c]^X, M ⊆ [0, 1]^X; reason: the setting of §3 (p. 18), under which Theorems 1.8 and 5.10 are proved; with P ⊆ [0, 1]^X the equivalence fails (see the mission's findings).
--   - reading: "realizable by propensity scores P and outcome regressions M" → some members of P and M are versions (a.s.) of p_D, m_{D,0}, m_{D,1}; reason: these functions are only defined almost everywhere.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 3 (PDF 5), Informal Theorem 1; with Problem 1 (p. 2), §3 (p. 18) and eq. (1) (p. 19)

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_SampleComplexity
import Definitions.Def_MinimaxATE_Learnability_FatDims

namespace MinimaxATE.Learnability

theorem informal_theorem_1 {X : Type*} [MeasurableSpace X] (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1 / 2)
    (P M : Set (X → ℝ)) (hP : ∀ p ∈ P, ∀ x, p x ∈ Set.Icc c (1 - c))
    (hM : ∀ m ∈ M, ∀ x, m x ∈ Set.Icc (0 : ℝ) 1) :
    Learnable P M c ↔ ∀ κ γ : ℝ, 0 < κ → 0 < γ → mutFat P M κ γ < ⊤ := by sorry

end MinimaxATE.Learnability
