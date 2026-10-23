-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_theorem_1
-- name    : InventoryAnomaly.EW.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:21.535986+00:00
-- url     : https://prove2.me/theorems/10a48cbf-9376-4544-9072-c03325bd77cf
-- title:
--   Theorem 1, p. 12 — the EW algorithm's expected excess cost over the oracle π* is O(log^1.5(m)/√m), polynomial in K, L, κ, μ, 1/p_O, r
-- statement:
--   Throughout, the standing assumptions of §2 (pp. 8–10) are in force: $2\le m\le n$; $M^*\in\mathbb R_+^{n\times m}$ has rank $r\ge 1$ with SVD $M^*=U\Sigma V^\top$, singular values $\sigma_1^*\ge\dots\ge\sigma_r^*>0$ and condition number $\kappa=\sigma_1^*/\sigma_r^*$; $\|M^*\|_{\max}\ge c_M$ and $\|M^*\|_{\max}\le L$; $\|U\|_{2,\infty}\le\sqrt{\mu r/n}$, $\|V\|_{2,\infty}\le\sqrt{\mu r/m}$; the sparsity condition $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$; $p_A^*\le 1-c_A$; $\alpha^*\in\Gamma$; $\|\mathrm{Anom}(\alpha^*,M^*_{ij})\|_{\psi_1}\le L$; $k\mapsto\mathbb P(\mathrm{Anom}(\alpha,M)=k)$ is $K$-Lipschitz in $(\alpha,M)\in\Gamma\times[0,\infty)$; and $\mathbb E\,\mathrm{Anom}(\alpha,M)=g(\alpha)M$ with $g:\mathbb R^d\to[0,1]$ $K$-Lipschitz.
--
--   Assume also Lemma 1's regularity conditions on $F(\theta)=(g_t(\theta,M^*e(\theta^*)/e(\theta)))_{t<T}$ with a constant $C_{RC}$, and costs $c^{(0)}_{ij},c^{(1)}_{ij}\in[0,c_{\max}]$. Let $\pi^{EW}$ be the entrywise algorithm run with any best rank-$r$ approximation $\mathrm{SVD}_r$ and any moment-matching estimate $\hat\theta\in\Theta$ with $h(\hat\theta)\le h(\theta^*)$, and $\pi^*$ the oracle threshold rule (4). There are constants $C_{sp}$, $C_0>0$ and an exponent $k\in\mathbb N$, depending only on $d$, $c_M$, $c_A$ and $C_{RC}$, such that for every instance
--   $$\mathbb E_{X_\Omega}\Big(\mathrm{cost}^{\pi^{EW}}(X_\Omega)-\mathrm{cost}^{\pi^*}(X_\Omega)\Big)\le c_{\max}\,C_0\,\big(1+K+L+\kappa+\mu+r+p_O^{-1}\big)^k\,\frac{\log^{1.5}(m)}{\sqrt m}.$$
--
--   This is the paper's main result: with a single cross-sectional snapshot, the EW algorithm's anomaly-detection cost approaches that of the oracle that knows $M^*$, $\alpha^*$ and $p_A^*$, at rate $\log^{1.5}(m)/\sqrt m$.
--
--   **Formalization Note.** "$O(\cdot)$ hides polynomial dependence on $K,L,\kappa,\mu,p_O^{-1}$ and $r$" is read as the factor $C_0(1+K+L+\kappa+\mu+r+1/p_O)^k$; the factor $c_{\max}$ is the proof's "$C=\max|c^{(0)}+c^{(1)}|$" (p. 24). Theorem 1 prints no hypotheses; the statement carries §2's assumptions, Lemma 1's regularity conditions (Appendix B: "it is sufficient to prove Lemmas 1 to 3") and bounded costs. The expectation is over the full sampling law of $(\Omega,B,X)$. The algorithm is quantified over every tie-breaking of its two arg-min steps.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 12, Theorem 1; proof sketch §5.1, pp. 22–24; Appendix B, pp. 42–47

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem theorem_1 (d : ℕ) (cM cA CRC : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1)
    (hCRC : 0 < CRC) :
    ∃ Csp C₀ : ℝ, ∃ k : ℕ, 0 < Csp ∧ 0 < C₀ ∧
      ∀ (I : Instance d) (K L μ cmax : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.Regular hI.r_pos cA CRC K L μ → I.CostBound cmax →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        ∫ ω, (I.costEW svdr θhat (I.obs ω) - I.costStar (I.obs ω)) ∂I.law ≤
          cmax * C₀ * (1 + K + L + I.κ hI.r_pos + μ + I.r + 1 / (I.pO : ℝ)) ^ k *
            Real.log I.m ^ ((3 : ℝ) / 2) / Real.sqrt I.m := by sorry

end InventoryAnomaly.EW
