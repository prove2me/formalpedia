-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_18
-- name    : InventoryAnomaly.EW.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:56.265727+00:00
-- url     : https://prove2.me/theorems/174a3c78-46e1-429a-9b8c-5915b89a385b
-- title:
--   Lemma 18, p. 45 — w.p. 1 − O(1/nm), max(|x̂_ij − x*_ij|, |ŷ_ij − y*_ij|) ≤ C(L + K)²Lδ′ for every (i, j) ∈ Ω (δ′ as in B.2)
-- statement:
--   Throughout, the standing assumptions of §2 (pp. 8–10) are in force: $2\le m\le n$; $M^*\in\mathbb R_+^{n\times m}$ has rank $r\ge 1$ with SVD $M^*=U\Sigma V^\top$, singular values $\sigma_1^*\ge\dots\ge\sigma_r^*>0$ and condition number $\kappa=\sigma_1^*/\sigma_r^*$; $\|M^*\|_{\max}\ge c_M$ and $\|M^*\|_{\max}\le L$; $\|U\|_{2,\infty}\le\sqrt{\mu r/n}$, $\|V\|_{2,\infty}\le\sqrt{\mu r/m}$; the sparsity condition $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$; $p_A^*\le 1-c_A$; $\alpha^*\in\Gamma$; $\|\mathrm{Anom}(\alpha^*,M^*_{ij})\|_{\psi_1}\le L$; $k\mapsto\mathbb P(\mathrm{Anom}(\alpha,M)=k)$ is $K$-Lipschitz in $(\alpha,M)\in\Gamma\times[0,\infty)$; and $\mathbb E\,\mathrm{Anom}(\alpha,M)=g(\alpha)M$ with $g:\mathbb R^d\to[0,1]$ $K$-Lipschitz.
--
--   Assume Lemma 1's regularity conditions (constant $C_{RC}$), let $\mathrm{SVD}_r$ be a best rank-$r$ approximation and $\hat\theta\in\Theta$ any estimator with $h(\hat\theta)\le h(\theta^*)$. Let $\hat x_{ij},\hat y_{ij}$ be the truncated plug-in estimates of Step 3 and $x^*_{ij}=p_A^*\mathbb P_{\mathrm{Anom}(\alpha^*,M^*_{ij})}(X_{ij})$, $y^*_{ij}=(1-p_A^*)\mathbb P_{\mathrm{Poisson}(M^*_{ij})}(X_{ij})$. In Appendix B.2, $\delta'$ denotes $(K+L)\kappa^4\mu rL\sqrt{\log(m)/(p_Om)}$. The constants $C_{sp}$ (how large the sparsity constant must be), $C$ and $C'$ depend only on $d=\dim\alpha$, $c_M$, $c_A$ and $C_{RC}$ such that, with probability at least $1-C'/(nm)$, for every $(i,j)\in\Omega$,
--   $$\max\big(|\hat x_{ij}-x^*_{ij}|,\ |\hat y_{ij}-y^*_{ij}|\big)\le C(L+K)^2L\cdot(K+L)\kappa^4\mu rL\sqrt{\frac{\log(m)}{p_Om}} .$$
--
--   Combined with Lemma 19 it yields Lemma 3.
--
--   **Formalization Note.** The B.2 redefinition of $\delta'$ is written out, so the formula multiplies the main-text $\delta'$ of p. 17 by $(K+L)$.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 45, Lemma 18 (δ′ as redefined in B.2, p. 45); proof p. 46

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_18 (d : ℕ) (cM cA CRC : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1)
    (hCRC : 0 < CRC) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.Regular hI.r_pos cA CRC K L μ →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω | ∀ ij ∈ I.omega (I.obs ω),
          max |I.xhat svdr θhat (I.obs ω) ij.1 ij.2 - I.xstar (I.obs ω) ij.1 ij.2|
              |I.yhat svdr θhat (I.obs ω) ij.1 ij.2 - I.ystar (I.obs ω) ij.1 ij.2| ≤
            C * (L + K) ^ 2 * L * ((K + L) * I.δ' hI.r_pos μ L)} := by sorry

end InventoryAnomaly.EW
