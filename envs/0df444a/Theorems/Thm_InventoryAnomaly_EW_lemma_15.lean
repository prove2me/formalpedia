-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_15
-- name    : InventoryAnomaly.EW.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:57.597713+00:00
-- url     : https://prove2.me/theorems/ae0661b4-ebc4-488e-a1c5-9f64524ab9b6
-- title:
--   Lemma 15, p. 42 — w.p. 1 − O(1/nm), uniformly over θ ∈ Θ and t ≤ T, |g_t(θ, M*e(θ*)/e(θ)) − g_t(θ, M̂/e(θ))| ≲ (K + L)δ′
-- statement:
--   Throughout, the standing assumptions of §2 (pp. 8–10) are in force: $2\le m\le n$; $M^*\in\mathbb R_+^{n\times m}$ has rank $r\ge 1$ with SVD $M^*=U\Sigma V^\top$, singular values $\sigma_1^*\ge\dots\ge\sigma_r^*>0$ and condition number $\kappa=\sigma_1^*/\sigma_r^*$; $\|M^*\|_{\max}\ge c_M$ and $\|M^*\|_{\max}\le L$; $\|U\|_{2,\infty}\le\sqrt{\mu r/n}$, $\|V\|_{2,\infty}\le\sqrt{\mu r/m}$; the sparsity condition $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$; $p_A^*\le 1-c_A$; $\alpha^*\in\Gamma$; $\|\mathrm{Anom}(\alpha^*,M^*_{ij})\|_{\psi_1}\le L$; $k\mapsto\mathbb P(\mathrm{Anom}(\alpha,M)=k)$ is $K$-Lipschitz in $(\alpha,M)\in\Gamma\times[0,\infty)$; and $\mathbb E\,\mathrm{Anom}(\alpha,M)=g(\alpha)M$ with $g:\mathbb R^d\to[0,1]$ $K$-Lipschitz.
--
--   Write $\delta'=\kappa^4\mu rL\sqrt{\log(m)/(p_Om)}$ (p. 17). Assume also the sparsity condition of p. 41 (as in Theorem 2), and let $\Theta=\Gamma\times[0,1-c_A]$. The constants $C_{sp}$ (how large the sparsity constant must be), $C$ and $C'$ depend only on $d=\dim\alpha$, $c_M$, $c_A$ such that, with probability at least $1-C'/(nm)$, for every $\theta\in\Theta$ and every $t=0,1,\dots,T$ (here $T=d+1$),
--   $$\Big|g_t\Big(\theta,\frac{M^*e(\theta^*)}{e(\theta)}\Big)-g_t\Big(\theta,\frac{\hat M}{e(\theta)}\Big)\Big|\le C(K+L)\delta' .$$
--
--   It transfers the entrywise accuracy of $\hat M$ to the model-implied CDF moments used by the moment-matching estimator.
--
--   **Formalization Note.** The constant may depend on $d$: the anomaly CDF at level $t\le T$ is a sum of $t+1$ $K$-Lipschitz pmf values. The p. 41 form of the sparsity condition is carried because the lemma's proof invokes Theorem 2.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 42, Lemma 15

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_15 (d : ℕ) (cM cA : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ),
        IsBestRankApprox I.r svdr →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω | ∀ θ ∈ I.Θ cA, ∀ t ≤ d + 1,
          |I.gt θ ((I.model.e I.θstar / I.model.e θ) • I.Mstar) t -
            I.gt θ ((I.model.e θ)⁻¹ • I.Mhat svdr (I.obs ω)) t| ≤
              C * (K + L) * I.δ' hI.r_pos μ L} := by sorry

end InventoryAnomaly.EW
