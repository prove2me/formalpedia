-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_1
-- name    : InventoryAnomaly.EW.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:01.067144+00:00
-- url     : https://prove2.me/theorems/e910f39d-0282-4ad8-9a09-32b0738aee5c
-- title:
--   Lemma 1, p. 17 — under the regularity conditions on F, w.p. 1 − O(1/nm), ‖θ̂ − θ*‖ ≤ C(K + L)κ⁴μrL√(log m/(p_O m)), i.e. Eq. (6)
-- statement:
--   Throughout, the standing assumptions of §2 (pp. 8–10) are in force: $2\le m\le n$; $M^*\in\mathbb R_+^{n\times m}$ has rank $r\ge 1$ with SVD $M^*=U\Sigma V^\top$, singular values $\sigma_1^*\ge\dots\ge\sigma_r^*>0$ and condition number $\kappa=\sigma_1^*/\sigma_r^*$; $\|M^*\|_{\max}\ge c_M$ and $\|M^*\|_{\max}\le L$; $\|U\|_{2,\infty}\le\sqrt{\mu r/n}$, $\|V\|_{2,\infty}\le\sqrt{\mu r/m}$; the sparsity condition $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$; $p_A^*\le 1-c_A$; $\alpha^*\in\Gamma$; $\|\mathrm{Anom}(\alpha^*,M^*_{ij})\|_{\psi_1}\le L$; $k\mapsto\mathbb P(\mathrm{Anom}(\alpha,M)=k)$ is $K$-Lipschitz in $(\alpha,M)\in\Gamma\times[0,\infty)$; and $\mathbb E\,\mathrm{Anom}(\alpha,M)=g(\alpha)M$ with $g:\mathbb R^d\to[0,1]$ $K$-Lipschitz.
--
--   Let $F(\theta)=(g_t(\theta,M^*e(\theta^*)/e(\theta)))_{t<T}$ on $\Theta=\Gamma\times[0,1-c_A]$ with $T=d+1$, $\delta'=\kappa^4\mu rL\sqrt{\log(m)/(p_Om)}$ and $\tilde\delta=\delta'(K+L)\log m$. Assume Lemma 1's regularity conditions with a constant $C_{RC}>0$:
--   1. $F$ is continuously differentiable and injective on $\Theta$;
--   2. $B_{\tilde\delta}(\theta^*)\subset\Theta$;
--   3. $\|J_F(\theta)-J_F(\theta^*)\|_2\le (C_{RC}/\tilde\delta)\|\theta-\theta^*\|$ for $\theta\in B_{\tilde\delta}(\theta^*)$;
--   4. $\|J_F(\theta^*)^{-1}\|_2\le C_{RC}$.
--
--   Let $\hat\theta\in\Theta$ be any estimator with $h(\hat\theta)\le h(\theta^*)$. The constants $C_{sp}$ (how large the sparsity constant must be), $C$ and $C'$ depend only on $d=\dim\alpha$, $c_M$, $c_A$ and $C_{RC}$ such that, with probability at least $1-C'/(nm)$, Eq. (6) holds:
--   $$\big\|\hat\theta-\theta^*\big\|\le C(K+L)\kappa^4\mu rL\sqrt{\frac{\log(m)}{p_Om}} .$$
--
--   This is the recovery guarantee for the moment-matching estimator (Step 2 of Algorithm 1).
--
--   **Formalization Note.** Both constants named $C$ in the regularity conditions are the single fixed $C_{RC}$, chosen before the existential constants. The estimator is any selector with $h(\hat\theta)\le h(\theta^*)$ (implied by being an arg min of (7)). The third condition is $\le (C/\tilde\delta)\|\theta-\theta^*\|$, read from the rendered page. $J_F$ is the Fréchet derivative of $F$ within $\Theta$ (one-sided at boundary points of $\Theta$), and $\|\cdot\|_2$ is the operator norm.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 17, Lemma 1; p. 16, eq. (6); proof p. 45

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_1 (d : ℕ) (cM cA CRC : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1)
    (hCRC : 0 < CRC) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.Regular hI.r_pos cA CRC K L μ →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω |
          ‖θhat (I.obs ω) - I.θstar‖ ≤ C * (K + L) * I.δ' hI.r_pos μ L} := by sorry

end InventoryAnomaly.EW
