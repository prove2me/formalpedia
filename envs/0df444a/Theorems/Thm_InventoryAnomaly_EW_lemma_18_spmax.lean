-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_18_spmax
-- name    : InventoryAnomaly.EW.lemma_18_spmax
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T08:57:21.709869+00:00
-- url     : https://prove2.me/theorems/3b45e5b6-ef0e-4ebc-ae89-b797a996697c
-- title:
--   Lemma 18, p. 45 (sparsity as read on p. 41) — plug-in terms x̂_ij, ŷ_ij within C(L + K)²Lδ′ of x_ij, y_ij on Ω
-- statement:
--   Throughout, the standing assumptions of §2 (pp. 8–10) are in force (as in the `InventoryAnomaly_EW_Model` definition: $2\le m\le n$, rank-$r$ SVD $M^*=U\Sigma V^\top$ with condition number $\kappa$, $c_M\le\|M^*\|_{\max}\le L$, $\mu$-incoherence, the sparsity condition $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$, $p_A^*\le 1-c_A$, and the three assumptions on $\mathrm{Anom}(\cdot,\cdot)$ with constants $K,L$). In addition we assume the sparsity condition **in the form in which the proof of Theorem 2 reads it** (p. 41): for the maximal entry $\|M^*\|_{\max}$,
--   $$\sqrt{p_O}\ \ge\ C_{sp}\,\frac{\log^{1.5}(m)\,\mu r L\kappa^2}{\|M^*\|_{\max}\sqrt m}.$$
--   The paper derives this from §2 ("By the assumption in Section 2"), which is only valid when $L/\|M^*\|_{\max}$ is bounded; the milestone Theorem 2 is formalized with this hypothesis (`SparsityMax`), so every result that rests on Theorem 2 must carry it too.
--
--   Assume Lemma 1's regularity conditions (constant $C_{RC}$), let $\mathrm{SVD}_r$ be a best rank-$r$ approximation and $\hat\theta\in\Theta$ any estimator with $h(\hat\theta)\le h(\theta^*)$. Let $\hat x_{ij}=[\hat p_A\,\mathbb P(\mathrm{Anom}(\hat\alpha,\hat M_{ij}/e(\hat\theta))=X_{ij})]$ and $\hat y_{ij}=[(1-\hat p_A)\,\mathbb P(\mathrm{Poisson}(\hat M_{ij}/e(\hat\theta))=X_{ij})]$ be the plug-in estimates truncated to $[0,1]$, and $x^*_{ij}=p_A^*\mathbb P(\mathrm{Anom}(\alpha^*,M^*_{ij})=X_{ij})$, $y^*_{ij}=(1-p_A^*)\mathbb P(\mathrm{Poisson}(M^*_{ij})=X_{ij})$. With $\delta'$ as redefined in B.2, $\delta'=(K+L)\kappa^4\mu rL\sqrt{\log(m)/(p_Om)}$, there are constants $C_{sp},C,C'>0$ depending only on $d,c_M,c_A,C_{RC}$ such that, with probability at least $1-C'/(nm)$, for every $(i,j)\in\Omega$,
--   $$\max\big(|\hat x_{ij}-x^*_{ij}|,\ |\hat y_{ij}-y^*_{ij}|\big)\le C(L+K)^2L\cdot(K+L)\kappa^4\mu rL\sqrt{\frac{\log m}{p_Om}}.$$
--
--   The paper's proof (p. 46) combines Lemma 1 ($\hat\theta\approx\theta^*$) and Theorem 2 ($\hat M\approx e(\theta^*)M^*$ entrywise) with the Lipschitz properties of the anomaly and Poisson probabilities.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 45, Lemma 18 (δ′ as redefined in B.2, p. 45); proof p. 46; sparsity assumption as read in the proof of Theorem 2, p. 41

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_18_spmax (d : ℕ) (cM cA CRC : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1)
    (hCRC : 0 < CRC) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        I.Regular hI.r_pos cA CRC K L μ →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω | ∀ ij ∈ I.omega (I.obs ω),
          max |I.xhat svdr θhat (I.obs ω) ij.1 ij.2 - I.xstar (I.obs ω) ij.1 ij.2|
              |I.yhat svdr θhat (I.obs ω) ij.1 ij.2 - I.ystar (I.obs ω) ij.1 ij.2| ≤
            C * (L + K) ^ 2 * L * ((K + L) * I.δ' hI.r_pos μ L)} := by sorry

end InventoryAnomaly.EW
