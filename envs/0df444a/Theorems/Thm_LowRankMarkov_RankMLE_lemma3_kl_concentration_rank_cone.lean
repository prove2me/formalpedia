-- Prove2me | Theorems.Thm_LowRankMarkov_RankMLE_lemma3_kl_concentration_rank_cone
-- name    : LowRankMarkov.RankMLE.lemma3_kl_concentration_rank_cone
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-20T20:40:37.391258+00:00
-- url     : https://prove2.me/theorems/c81bc403-4ed9-4bd7-9d54-bdecc0efcefa
-- title:
--   Lemma 3, (8), p. 14 — uniform concentration of D̃_KL(P,Q) around D_KL(P,Q) over the cone ‖Q−P‖_* ≤ 4(2r)^{1/2}‖Q−P‖_F
-- statement:
--   This is Lemma 3 of Zhu, Li, Wang and Zhang, the uniform concentration of the empirical Kullback–Leibler divergence. Here the nuclear-norm cone in the class $\mathcal C$ uses the rank-dependent converting factor $4(2r)^{1/2}$.
--
--   Let $p\ge2$ and $\alpha,\beta>0$. Let $X_0,X_1,\dots,X_n$ be a Markov chain on $p$ states started from its stationary distribution $\pi$ (all $\pi_i>0$). Its transition matrix $P$ is primitive, has rank $r$, and satisfies Assumption 1:
--   $$P_{jk}\in\{0\}\cup[\alpha/p,\beta/p]\quad\text{for all }j,k.$$
--   Write $\pi_{\min},\pi_{\max}$ for the extreme stationary probabilities and $1-\rho_+$ for the right $L_2(\pi)$ spectral gap. For a stochastic matrix $Q$ with positive entries, let
--   $$D_{\mathrm{KL}}(P,Q)=\sum_{i,j}\pi_iP_{ij}\log\frac{P_{ij}}{Q_{ij}},\qquad \widetilde D_{\mathrm{KL}}(P,Q)=\ell_n(Q)-\ell_n(P),$$
--   where $\ell_n(Q)=-\frac1n\sum_{i,j}n_{ij}\log Q_{ij}$ is the averaged negative log-likelihood and $n_{ij}$ are the transition counts. Define
--   $$\mathcal C_r=\Big\{Q:\ \|Q-P\|_*\le 4(2r)^{1/2}\|Q-P\|_F,\ Q1_p=1_p,\ \alpha/p\le Q_{jk}\le\beta/p\ \ \forall j,k\Big\}.$$
--
--   There exist universal constants $C_1,C_2>0$ such that the following holds. Suppose
--   $$n\pi_{\max}(1-\rho_+)\ge\max(20\log p,\log n),$$
--   and let $\eta>\pi_{\min}/(2\pi_{\max}rp\log p)$. Then
--   $$\mathbb P\Big\{\forall Q\in\mathcal C_r\text{ with }D_{\mathrm{KL}}(P,Q)\ge\eta:\ \big|\widetilde D_{\mathrm{KL}}(P,Q)-D_{\mathrm{KL}}(P,Q)\big|\le\tfrac12D_{\mathrm{KL}}(P,Q)+\frac{C_1\pi_{\max}\beta^2rp\log p}{\pi_{\min}\alpha^3n}\Big\}\ge1-C_2\exp\Big(-\frac{\eta\pi_{\max}rp\log p}{\pi_{\min}}\Big).$$
--
--   The lemma is the probabilistic core of both statistical guarantees in the paper. The difference $\widehat P-P$ of the nuclear-norm estimator lies in the cone by Lemma 1, (7). The difference $\widehat P^r-P$ of the rank-constrained estimator satisfies $\|\widehat P^r-P\|_*\le(2r)^{1/2}\|\widehat P^r-P\|_F$ by the rank remark on p. 14. So with this class, Lemma 3 applies to both estimators, as the paper asserts ("Lemma 3 remains applicable in the statistical analysis of $\widehat P^r$"). Because $4\sqrt2\le4\sqrt{2r}$ for $r\ge1$, this statement also implies the version over the printed class $\mathcal C$, whose cone factor is $4\times2^{1/2}$.
--
--   **Formalization Note** The printed class $\mathcal C$ on p. 14 has cone factor $4\times 2^{1/2}$. That class does not contain $\widehat P^r$ when $r>16$, so it cannot support the paper's derivation of Theorem 2 from Lemma 3. The factor $4(2r)^{1/2}$ is the converting factor printed in (7), and the shells $\mathcal C_l$ in the proof (p. ec9) are controlled through the factor $(2r)^{1/2}$ in (EC.14). The probability is over the chain law with $X_0\sim\pi$ (a finite sum over trajectories). The constants $C_1,C_2$ are chosen before all data.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. 14, Lemma 3 (8); cone factor 4(2r)^{1/2} from Lemma 1, (7), p. 13, and the rank remark at the end of §3.3, p. 14; proof pp. ec9–ec11 (shells C_l, (EC.14))

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting

namespace LowRankMarkov.RankMLE

open CaiCandesShen.Convergence

/-- Lemma 3, (8), p. 14, arXiv:1907.00113v2, with `X₀ ∼ π`, over the class `𝒞` whose
nuclear-norm cone carries the rank-dependent converting factor `4(2r)^{1/2}` of Lemma 1, (7):
`‖Q − P‖_* ≤ 4(2r)^{1/2}‖Q − P‖_F`. This is the reading under which Lemma 3 applies both to
`P̂ − P` (by (7)) and to `P̂^r − P` (by the rank remark on p. 14). The universal constants
`C₁, C₂` are quantified before all data. -/
theorem lemma3_kl_concentration_rank_cone :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (p r n : ℕ) (α β : ℝ) (P : Matrix (Fin p) (Fin p) ℝ) (π : Fin p → ℝ),
        2 ≤ p → 0 < α → 0 < β →
        IsStochastic P → IsStationary π P → (∀ i, 0 < π i) → IsPrimitive P →
        Assumption1 α β r P →
        max (20 * Real.log p) (Real.log n) ≤ n * piMax π * (1 - rhoPlus π P) →
        ∀ η : ℝ, piMin π / (2 * piMax π * r * p * Real.log p) < η →
          1 - C₂ * Real.exp (-(η * piMax π * r * p * Real.log p / piMin π)) ≤
            trajProb π P (fun x : Fin (n + 1) → Fin p => ∀ Q : Matrix (Fin p) (Fin p) ℝ,
              nuclearNorm (Q - P) ≤ 4 * Real.sqrt (2 * (r : ℝ)) * frobNorm (Q - P) →
              (∀ i, ∑ j, Q i j = 1) →
              (∀ i j, α / (p : ℝ) ≤ Q i j ∧ Q i j ≤ β / (p : ℝ)) →
              η ≤ klDiv π P Q →
                |empKL x P Q - klDiv π P Q| ≤
                  (1 / 2) * klDiv π P Q +
                    C₁ * piMax π * β ^ 2 * r * p * Real.log p / (piMin π * α ^ 3 * n)) := by sorry

end LowRankMarkov.RankMLE
