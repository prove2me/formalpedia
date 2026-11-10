-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_theorem_5_10
-- name    : MinimaxATE.Learnability.theorem_5_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:02:19.419308+00:00
-- url     : https://prove2.me/theorems/018d9bcc-4ed8-4814-b370-18880a5f235c
-- title:
--   Theorem 5.10 — $N_{\mathrm{ATE}}(\varepsilon,\delta)\gtrsim_c(\kappa\gamma/\varepsilon)\,k/\log^4(2k+1/\varepsilon)$ for every $k\le\mathrm{fat}^{\mathrm{mut}}_{\kappa,\gamma}$
-- statement:
--   Fix $c\in(0,1/2)$. There are constants $c_0,B_c,a_c>0$ depending only on $c$ such that the following holds for every measurable space $\mathcal X$, all classes $\mathcal P\subseteq[c,1-c]^{\mathcal X}$, $\mathcal M\subseteq[0,1]^{\mathcal X}$ and scales $\kappa,\gamma>0$. Let $\varepsilon,\delta\in(0,1/8)$ with $\varepsilon\le c_0\kappa\gamma$, and let $k\in\mathbb N$ with $k\le\mathrm{fat}^{\mathrm{mut}}_{\kappa,\gamma}(\mathcal P,\mathcal M)$. Put
--   $$\mathrm{RHS}=\frac{\kappa\gamma}{\varepsilon}\cdot\frac{k}{\log^4(2k+1/\varepsilon)} .$$
--   If $\mathrm{RHS}\ge B_c/(\kappa\varepsilon)$, then
--   $$N_{\mathrm{ATE}}(\varepsilon,\delta)\ge a_c\cdot\mathrm{RHS}.$$
--   With $k=\mathrm{fat}^{\mathrm{mut}}_{\kappa,\gamma}(\mathcal P,\mathcal M)$ (when finite) this is the paper's lower bound; letting $k$ grow when the dimension is infinite gives the "only if" direction of the main characterization.
--
--   **Formalization Note.** $N_{\mathrm{ATE}}$ is cast from `ℕ∞` to `ℝ≥0∞`. As printed the statement is false over a $\sigma$-algebra that does not separate points (see the mission's findings); it is stated as printed, for every measurable space.
--
--   Differences from the source:
--   - generalization: the bound at k = fat^mut_{κ,γ}(P, M) → the bound for every natural k ≤ fat^mut_{κ,γ}(P, M); reason: k = fat^mut gives the printed statement when the dimension is finite, and the printed right-hand side is undefined when it is infinite; the proof only uses a k-point mutually shattered set.
--   - reading: "constants c₀, B_c", ε ≲_c κγ, N_ATE ≳_c → c₀, B_c, a_c > 0 chosen after c and before X, P, M, κ, γ, ε, δ, k, with ε ≤ c₀κγ and N_ATE ≥ a_c·RHS; reason: the paper's convention for c-dependent constants.
--   - reading: "every ATE estimator requires N_ATE(ε, δ) ≳_c …" → a lower bound on N_ATE(ε, δ; P, M, c); reason: N_ATE (eq. (1)) is the minimum over all measurable estimators.
--   - reading: concept classes P, M → P ⊆ [c, 1−c]^X, M ⊆ [0, 1]^X; reason: the standing setting of §3 (p. 18).
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 43 (PDF 45), Theorem 5.10

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_SampleComplexity
import Definitions.Def_MinimaxATE_Learnability_FatDims

namespace MinimaxATE.Learnability

universe u

theorem theorem_5_10 : ∀ (c : ℝ), 0 < c → c < 1 / 2 →
    ∃ c₀ B a : ℝ, 0 < c₀ ∧ 0 < B ∧ 0 < a ∧
    ∀ (X : Type u) [MeasurableSpace X] (P M : Set (X → ℝ)),
      (∀ p ∈ P, ∀ x, p x ∈ Set.Icc c (1 - c)) → (∀ m ∈ M, ∀ x, m x ∈ Set.Icc (0 : ℝ) 1) →
    ∀ (κ γ : ℝ), 0 < κ → 0 < γ →
    ∀ (ε δ : ℝ), 0 < ε → ε < 1 / 8 → 0 < δ → δ < 1 / 8 → ε ≤ c₀ * κ * γ →
    ∀ (k : ℕ), (k : ℕ∞) ≤ mutFat P M κ γ →
      B / (κ * ε) ≤ (κ * γ / ε) * (k : ℝ) / Real.log (2 * k + 1 / ε) ^ 4 →
      ENNReal.ofReal (a * ((κ * γ / ε) * (k : ℝ) / Real.log (2 * k + 1 / ε) ^ 4)) ≤
        ((NATE ε δ P M c : ℕ∞) : ENNReal) := by sorry

end MinimaxATE.Learnability
