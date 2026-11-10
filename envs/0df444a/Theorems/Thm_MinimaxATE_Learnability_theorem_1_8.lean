-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_theorem_1_8
-- name    : MinimaxATE.Learnability.theorem_1_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:02:03.205228+00:00
-- url     : https://prove2.me/theorems/d8599e64-8941-488e-be56-de68b3ffb1cb
-- title:
--   Theorem 1.8 — sample complexity upper bound: $N_{\mathrm{ATE}}\lesssim_c$ the better of the mutual fat-shattering and doubly robust rates
-- statement:
--   Fix the overlap $c\in(0,1/2)$. There are constants $C,c_1,c_2>0$ depending only on $c$ such that for every measurable space $\mathcal X$, all classes $\mathcal P\subseteq[c,1-c]^{\mathcal X}$, $\mathcal M\subseteq[0,1]^{\mathcal X}$ and every $\varepsilon,\delta\in(0,1)$,
--   $$N_{\mathrm{ATE}}(\varepsilon,\delta)\le C\Big(\frac{\log(2/\delta)}{\varepsilon^2}+\log^3\!\Big(\frac2\varepsilon\Big)\min\Big\{\frac{\mathrm{fat}^{\mathrm{mut}}_{c_1\varepsilon,c_1\varepsilon}(\mathcal P,\mathcal M)}{\varepsilon^2},\ N_{\mathrm{DR}}(\varepsilon,c_2,\mathcal P,\mathcal M)\Big\}\Big).$$
--
--   This is the paper's upper bound; finiteness of the mutual fat-shattering dimension at every scale makes the right-hand side finite, which is the "if" direction of the main characterization.
--
--   **Formalization Note.** Both sides live in $[0,\infty]$ (`ℝ≥0∞`); $N_{\mathrm{ATE}}$ is cast from `ℕ∞`, so the statement is meaningful (and nontrivial) when the right-hand side is finite. The logarithms are natural and positive here ($2/\delta,2/\varepsilon>2$).
--
--   Differences from the source:
--   - reading: "for every ε, δ ∈ (0, 1) and D ∈ D(P, M, c), there is an ATE estimator with N_ATE(ε, δ) ≲_c …" → a bound on N_ATE(ε, δ; P, M, c); reason: N_ATE (eq. (1)) already asserts one measurable estimator that works uniformly over D(P, M, c).
--   - reading: ≲_c and "constants c₁, c₂ that depend on the overlap c" → explicit C, c₁, c₂ > 0 chosen after c and before X, P, M, ε, δ; reason: the paper's convention for c-dependent constants.
--   - reading: concept classes P, M → P ⊆ [c, 1−c]^X, M ⊆ [0, 1]^X; reason: the standing setting of §3 (p. 18).
--   - encoding: real right-hand side, possibly infinite (fat^mut or N_DR = ∞) → comparison in [0, ∞] (ENNReal), N_ATE cast from ℕ∞; reason: Lean convention; the log factors are positive for ε, δ ∈ (0, 1), so no 0·∞ collapse.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 11 (PDF 13), Theorem 1.8; restated p. 19-20 (PDF 21-22)

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_SampleComplexity
import Definitions.Def_MinimaxATE_Learnability_FatDims

namespace MinimaxATE.Learnability

universe u

theorem theorem_1_8 : ∀ (c : ℝ), 0 < c → c < 1 / 2 →
    ∃ C c₁ c₂ : ℝ, 0 < C ∧ 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (X : Type u) [MeasurableSpace X] (P M : Set (X → ℝ)),
      (∀ p ∈ P, ∀ x, p x ∈ Set.Icc c (1 - c)) → (∀ m ∈ M, ∀ x, m x ∈ Set.Icc (0 : ℝ) 1) →
    ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ((NATE ε δ P M c : ℕ∞) : ENNReal) ≤
        ENNReal.ofReal C *
          (ENNReal.ofReal (Real.log (2 / δ) / ε ^ 2) +
            ENNReal.ofReal (Real.log (2 / ε) ^ 3) *
              min ((mutFat P M (c₁ * ε) (c₁ * ε) : ENNReal) / ENNReal.ofReal (ε ^ 2))
                (NDR ε c₂ P M)) := by sorry

end MinimaxATE.Learnability
