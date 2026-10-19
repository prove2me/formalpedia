-- Prove2me | Theorems.Thm_LowRankMarkov_RankMLE_lemma3_uniform_kl_concentration
-- name    : LowRankMarkov.RankMLE.lemma3_uniform_kl_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:13.618311+00:00
-- url     : https://prove2.me/theorems/24176ce1-a620-473d-9309-8327dfac82e6
-- title:
--   Lemma 3, (8), p. 14 — uniform concentration of D̃_KL(P, Q) around D_KL(P, Q) over rank-constrained Q with D_KL(P, Q) ≥ η
-- statement:
--   There exist universal constants $C_1,C_2>0$ with the following property. Let $p\ge2$, $\alpha,\beta>0$, and let $X_0,\dots,X_n$ be the Markov chain with a primitive transition matrix $P$ satisfying Assumption 1 (rank $r$, $P_{jk}\in\{0\}\cup[\alpha/p,\beta/p]$), started from its stationary distribution $\pi$ (all $\pi_i>0$). Suppose
--   $$n\pi_{\max}(1-\rho_+)\ \ge\ \max(20\log p,\log n).$$
--   Then for every $\eta>\pi_{\min}/(2\pi_{\max}rp\log p)$,
--   $$\mathbb P\Big\{\forall Q\in\mathcal C(\eta):\ \big|\widetilde D_{\mathrm{KL}}(P,Q)-D_{\mathrm{KL}}(P,Q)\big|\le\tfrac12D_{\mathrm{KL}}(P,Q)+\frac{C_1\pi_{\max}\beta^2rp\log p}{\pi_{\min}\alpha^3n}\Big\}\ \ge\ 1-C_2\exp\Big(-\frac{\eta\pi_{\max}rp\log p}{\pi_{\min}}\Big),$$
--   where $\mathcal C(\eta)$ is the set of $Q$ with $Q1_p=1_p$, $\alpha/p\le Q_{jk}\le\beta/p$, $\|Q-P\|_*\le4\sqrt2\|Q-P\|_F$, and $D_{\mathrm{KL}}(P,Q)\ge\eta$.
--
--   This uniform law is the probabilistic core of Theorem 2: on its event, the empirical KL divergence controls the population KL divergence for every candidate estimator simultaneously.
--
--   **Formalization Note** The statement uses the printed class $\mathcal C$, with its nuclear-norm cone and no rank constraint. The appendix proof works on shells that add $\operatorname{rank}(Q)\le r$, leaving a gap for the printed class; the p. 14 claim that Lemma 3 applies to the rank-constrained estimator also needs a separate argument when $r>16$. The chain starts at stationarity ($X_0\sim\pi$); $C_1,C_2$ precede all data; $p\ge2$ keeps $\log p>0$.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. 14, Lemma 3, (8); set C and D̃_KL, p. 14; proof EC.8, pp. ec8–ec11 (PDF pp. 41–44)

import Mathlib
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting

namespace LowRankMarkov.RankMLE

/-- Lemma 3, (8), p. 14, arXiv:1907.00113v2, over the printed cone class `𝒞`
and with `X₀ ∼ π`: if `nπ_max(1 − ρ₊) ≥ max(20 log p, log n)`,
then for every `η > π_min/(2π_max r p log p)`, with probability at least
`1 − C₂ exp(−ηπ_max r p log p/π_min)`, every `Q ∈ 𝒞` with `D_KL(P, Q) ≥ η` satisfies
`|D̃_KL(P, Q) − D_KL(P, Q)| ≤ ½ D_KL(P, Q) + C₁π_max β² r p log p/(π_min α³ n)`. The universal
constants `C₁, C₂` are quantified before all data. -/
theorem lemma3_uniform_kl_concentration :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (p r n : ℕ) (α β : ℝ) (P : Matrix (Fin p) (Fin p) ℝ) (π : Fin p → ℝ),
        2 ≤ p → 0 < α → 0 < β →
        IsStochastic P → IsStationary π P → (∀ i, 0 < π i) → IsPrimitive P →
        Assumption1 α β r P →
        max (20 * Real.log p) (Real.log n) ≤ n * piMax π * (1 - rhoPlus π P) →
        ∀ η : ℝ, piMin π / (2 * piMax π * r * p * Real.log p) < η →
          1 - C₂ * Real.exp (-(η * piMax π * r * p * Real.log p / piMin π)) ≤
            trajProb π P (fun x : Fin (n + 1) → Fin p => ∀ Q : Matrix (Fin p) (Fin p) ℝ,
              ConcentrationClass α β P Q → η ≤ klDiv π P Q →
                |empKL x P Q - klDiv π P Q| ≤
                  (1 / 2) * klDiv π P Q +
                    C₁ * piMax π * β ^ 2 * r * p * Real.log p / (piMin π * α ^ 3 * n)) := by sorry

end LowRankMarkov.RankMLE
