-- Prove2me | Theorems.Thm_LowRankMarkov_RankMLE_theorem2_kl_tail_bound
-- name    : LowRankMarkov.RankMLE.theorem2_kl_tail_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:23.097528+00:00
-- url     : https://prove2.me/theorems/d89fa41e-ff38-420d-9946-3ed5df9b436e
-- title:
--   Theorem 2 (KL display), p. 10 — ℙ{D_KL(P, P̂^r) ≥ max(C₁rπ_maxβ²p log p/(π_minα³n), ξπ_min/(rpπ_max log p))} ≤ C₂e^{−ξ}, under minoration
-- statement:
--   There exist universal constants $C_1,C_2>0$ with the following property. Let $p\ge2$, $\alpha,\beta>0$, and let $X_0,\dots,X_n$ be the Markov chain on $p$ states with a primitive transition matrix $P$ of rank $r$, started from its stationary distribution $\pi$ (all $\pi_i>0$). Assume the $(\alpha/p)$-minoration of Remark 2,
--   $$\alpha/p\le P_{jk}\le\beta/p\quad\text{for all }j,k,$$
--   and the spectral-gap condition
--   $$n\pi_{\max}(1-\rho_+)>\max(20\log p,\log n).$$
--   Let $\widehat P^r$ be any rank-constrained maximum likelihood estimator (5), i.e. any minimizer of $\ell_n(Q)$ subject to $Q1_p=1_p$, $\alpha/p\le Q_{ij}\le\beta/p$ and $\operatorname{rank}(Q)\le r$, chosen as an arbitrary function of the trajectory. Then for every $\xi>0$,
--   $$\mathbb P\Big\{D_{\mathrm{KL}}(P,\widehat P^r)\ge\max\Big(\frac{C_1r\pi_{\max}\beta^2p\log p}{\pi_{\min}\alpha^3n},\ \frac{\xi\pi_{\min}}{rp\pi_{\max}\log p}\Big)\Big\}\le C_2e^{-\xi}.$$
--
--   This is the paper's statistical guarantee for the rank-constrained estimator: with high probability its KL error is of order $rp\log p/n$, up to the factors $\pi_{\max}/\pi_{\min}$ and $\beta^2/\alpha^3$, plus a term that does not depend on $n$.
--
--   **Formalization Note** The printed Theorem 2 assumes Assumption 1, which allows $P_{jk}=0$; the statement is false then. Every feasible $Q$ has all entries at least $\alpha/p$, so a row of $P$ with zeros keeps a KL bias that does not shrink with $n$: for even $p$, take rows $1,\dots,p/2$ of $P$ equal to $2/p$ on columns $p/2+1,\dots,p$ and $0$ elsewhere, and rows $p/2+1,\dots,p$ equal to $1/p$; then $\operatorname{rank}P=2$, $\alpha=1$, $\beta=2$, $\rho_+=0$, $\pi_{\max}/\pi_{\min}=2$, every feasible $Q$ has $D_{\mathrm{KL}}(P,Q)\ge\tfrac13\log2$, and with $\xi=0.9\,p\log p$ the threshold is below $\tfrac13\log2$ for all large $n$, so the left side equals $1$, while $C_2e^{-\xi}<1$ once $p$ is large. The broken step is (EC.3), which needs $P$ feasible for (5). The statement therefore assumes Remark 2's minoration in place of Assumption 1(ii); Assumption 1(i), $\operatorname{rank}P=r$, is kept. The initial state is drawn from $\pi$, a hypothesis of Theorem 1 that the proof of Theorem 2 uses through Lemma 3. "Ergodic" is read as primitive; $\pi_i>0$ is implied by stationarity and primitivity and is stated to avoid a degenerate $\pi_{\min}$. $p\ge2$ keeps $\log p>0$ in the denominators; $n\ge1$ follows from the gap condition. $C_1,C_2$ are chosen before all data, including the estimator. The Frobenius-norm display of Theorem 2 is not part of this statement.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. 10, Theorem 2 (first display); proof EC.3, pp. ec2–ec3 (PDF pp. 35–36); minoration from Remark 2, p. 8; X₀ ∼ π from Theorem 1, p. 9

import Mathlib
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting

namespace LowRankMarkov.RankMLE

/-- Theorem 2, first (KL) display, p. 10, arXiv:1907.00113v2, under Remark 2's `(α/p)`-minoration
in place of Assumption 1(ii) and with `X₀ ∼ π`. The universal constants `C₁, C₂` are quantified
before all data; the bound holds for every selection `est` of the rank-constrained MLE (5). -/
theorem theorem2_kl_tail_bound :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (p r n : ℕ) (α β : ℝ) (P : Matrix (Fin p) (Fin p) ℝ) (π : Fin p → ℝ),
        2 ≤ p → 0 < α → 0 < β →
        IsStochastic P → IsStationary π P → (∀ i, 0 < π i) → IsPrimitive P →
        P.rank = r → Minorated α β P →
        max (20 * Real.log p) (Real.log n) < n * piMax π * (1 - rhoPlus π P) →
        ∀ (est : (Fin (n + 1) → Fin p) → Matrix (Fin p) (Fin p) ℝ),
          (∀ x, IsRankMLE α β r x (est x)) →
          ∀ ξ : ℝ, 0 < ξ →
            trajProb π P (fun x : Fin (n + 1) → Fin p =>
              max (C₁ * r * piMax π * β ^ 2 * p * Real.log p / (piMin π * α ^ 3 * n))
                  (ξ * piMin π / (r * p * piMax π * Real.log p))
                ≤ klDiv π P (est x)) ≤ C₂ * Real.exp (-ξ) := by sorry

end LowRankMarkov.RankMLE
