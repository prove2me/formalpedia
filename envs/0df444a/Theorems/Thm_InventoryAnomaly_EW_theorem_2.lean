-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_theorem_2
-- name    : InventoryAnomaly.EW.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:09.415162+00:00
-- url     : https://prove2.me/theorems/3e337ab4-5033-47af-a80b-0171b565d537
-- title:
--   Theorem 2, p. 16 — under the sparsity assumption as read on p. 41: w.p. 1 − O(1/nm), ‖M̂ − e(θ*)M*‖_max ≤ Cκ⁴μrL√(log m/(p_O m))
-- statement:
--   Throughout, the standing assumptions of §2 (pp. 8–10) are in force: $2\le m\le n$; $M^*\in\mathbb R_+^{n\times m}$ has rank $r\ge 1$ with SVD $M^*=U\Sigma V^\top$, singular values $\sigma_1^*\ge\dots\ge\sigma_r^*>0$ and condition number $\kappa=\sigma_1^*/\sigma_r^*$; $\|M^*\|_{\max}\ge c_M$ and $\|M^*\|_{\max}\le L$; $\|U\|_{2,\infty}\le\sqrt{\mu r/n}$, $\|V\|_{2,\infty}\le\sqrt{\mu r/m}$; the sparsity condition $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$; $p_A^*\le 1-c_A$; $\alpha^*\in\Gamma$; $\|\mathrm{Anom}(\alpha^*,M^*_{ij})\|_{\psi_1}\le L$; $k\mapsto\mathbb P(\mathrm{Anom}(\alpha,M)=k)$ is $K$-Lipschitz in $(\alpha,M)\in\Gamma\times[0,\infty)$; and $\mathbb E\,\mathrm{Anom}(\alpha,M)=g(\alpha)M$ with $g:\mathbb R^d\to[0,1]$ $K$-Lipschitz.
--
--   Assume moreover the sparsity condition in the form the proof of Theorem 2 uses it (p. 41): $C_{sp}\log^{1.5}(m)\mu rL\kappa^2/(\|M^*\|_{\max}\sqrt m)\le\sqrt{p_O}$. Let $\hat M=\frac{nm}{|\Omega|}\mathrm{SVD}(X_\Omega)_r$ be the rescaled best rank-$r$ approximation of the zero-filled observations and $e(\theta^*)=p_A^*g(\alpha^*)+1-p_A^*$. The constants $C_{sp}$ (how large the sparsity constant must be), $C$ and $C'$ depend only on $d=\dim\alpha$, $c_M$, $c_A$ such that for every instance, with probability at least $1-C'/(nm)$,
--   $$\big\|\hat M-e(\theta^*)M^*\big\|_{\max}\le C\kappa^4\mu rL\sqrt{\frac{\log(m)}{p_Om}} .$$
--
--   This is the paper's entrywise guarantee for matrix completion with sub-exponential (e.g. Poisson) noise and is the first step of the proof of Theorem 1.
--
--   **Formalization Note.** "With probability $1-O(1/nm)$" and the constant $C$ become existential constants chosen before the instance. The p. 41 form of the sparsity condition is added because the proof reads §2's assumption that way; with p. 10's form alone and a universal $C$ the bound is not what the proof delivers when $L/\|M^*\|_{\max}$ is large. `SVD_r` is any exact best rank-$\le r$ approximation.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 16, Theorem 2; proof pp. 41–42 (sparsity as read on p. 41)

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem theorem_2 (d : ℕ) (cM cA : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ),
        IsBestRankApprox I.r svdr →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω | maxNorm
            (I.Mhat svdr (I.obs ω) - I.model.e I.θstar • I.Mstar)
            (C * I.δ' hI.r_pos μ L)} := by sorry

end InventoryAnomaly.EW
