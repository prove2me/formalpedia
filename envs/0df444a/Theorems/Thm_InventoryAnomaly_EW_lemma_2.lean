-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_2
-- name    : InventoryAnomaly.EW.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:53.256972+00:00
-- url     : https://prove2.me/theorems/90cb410b-9635-4cae-887a-81bea7aa17e2
-- title:
--   Lemma 2, p. 23 — w.p. 1 − O(1/nm), ‖F(θ̂) − F(θ*)‖ ≤ C(K + L)κ⁴μrL√(log m/(p_O m))
-- statement:
--   Throughout, the standing assumptions of §2 (pp. 8–10) are in force: $2\le m\le n$; $M^*\in\mathbb R_+^{n\times m}$ has rank $r\ge 1$ with SVD $M^*=U\Sigma V^\top$, singular values $\sigma_1^*\ge\dots\ge\sigma_r^*>0$ and condition number $\kappa=\sigma_1^*/\sigma_r^*$; $\|M^*\|_{\max}\ge c_M$ and $\|M^*\|_{\max}\le L$; $\|U\|_{2,\infty}\le\sqrt{\mu r/n}$, $\|V\|_{2,\infty}\le\sqrt{\mu r/m}$; the sparsity condition $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$; $p_A^*\le 1-c_A$; $\alpha^*\in\Gamma$; $\|\mathrm{Anom}(\alpha^*,M^*_{ij})\|_{\psi_1}\le L$; $k\mapsto\mathbb P(\mathrm{Anom}(\alpha,M)=k)$ is $K$-Lipschitz in $(\alpha,M)\in\Gamma\times[0,\infty)$; and $\mathbb E\,\mathrm{Anom}(\alpha,M)=g(\alpha)M$ with $g:\mathbb R^d\to[0,1]$ $K$-Lipschitz.
--
--   Assume also the sparsity condition of p. 41. Let $F(\theta)=(F_t(\theta))_{t<T}$ with $F_t(\theta)=g_t(\theta,M^*e(\theta^*)/e(\theta))$ and $T=d+1$, and let $\hat\theta\in\Theta$ be any estimator with $h(\hat\theta)\le h(\theta^*)$ (in particular any minimiser of (7)). The constants $C_{sp}$ (how large the sparsity constant must be), $C$ and $C'$ depend only on $d=\dim\alpha$, $c_M$, $c_A$ such that, with probability at least $1-C'/(nm)$,
--   $$\big\|F(\hat\theta)-F(\theta^*)\big\|\le C(K+L)\kappa^4\mu rL\sqrt{\frac{\log(m)}{p_Om}} .$$
--
--   This is the first half of the recovery guarantee for $\hat\theta$; Lemma 17 inverts $F$ to obtain Lemma 1.
--
--   **Formalization Note.** The estimator is quantified over every selector with $\hat\theta\in\Theta$ and $h(\hat\theta)\le h(\theta^*)$, which is exactly what the proof uses (p. 43) and is implied by being an arg min. The p. 41 form of the sparsity condition is carried because the proof uses Theorem 2 via Lemma 15.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 23, Lemma 2; proof pp. 43–44

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_2 (d : ℕ) (cM cA : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω |
          ‖I.F (θhat (I.obs ω)) - I.F I.θstar‖ ≤ C * (K + L) * I.δ' hI.r_pos μ L} := by sorry

end InventoryAnomaly.EW
