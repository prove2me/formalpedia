-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_16
-- name    : InventoryAnomaly.EW.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:57.034507+00:00
-- url     : https://prove2.me/theorems/c4d7bc3b-b561-4757-9a21-976483354bc4
-- title:
--   Lemma 16, p. 43 — w.p. 1 − O(1/nm), the moment-matching objective at the truth satisfies h(θ*) ≲ (K + L)²(δ′)²
-- statement:
--   Throughout, the standing assumptions of §2 (pp. 8–10) are in force: $2\le m\le n$; $M^*\in\mathbb R_+^{n\times m}$ has rank $r\ge 1$ with SVD $M^*=U\Sigma V^\top$, singular values $\sigma_1^*\ge\dots\ge\sigma_r^*>0$ and condition number $\kappa=\sigma_1^*/\sigma_r^*$; $\|M^*\|_{\max}\ge c_M$ and $\|M^*\|_{\max}\le L$; $\|U\|_{2,\infty}\le\sqrt{\mu r/n}$, $\|V\|_{2,\infty}\le\sqrt{\mu r/m}$; the sparsity condition $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$; $p_A^*\le 1-c_A$; $\alpha^*\in\Gamma$; $\|\mathrm{Anom}(\alpha^*,M^*_{ij})\|_{\psi_1}\le L$; $k\mapsto\mathbb P(\mathrm{Anom}(\alpha,M)=k)$ is $K$-Lipschitz in $(\alpha,M)\in\Gamma\times[0,\infty)$; and $\mathbb E\,\mathrm{Anom}(\alpha,M)=g(\alpha)M$ with $g:\mathbb R^d\to[0,1]$ $K$-Lipschitz.
--
--   Write $\delta'=\kappa^4\mu rL\sqrt{\log(m)/(p_Om)}$ (p. 17). Assume also the sparsity condition of p. 41. Let $h$ be the moment-matching objective (7) with $T=d+1$ moments. The constants $C_{sp}$ (how large the sparsity constant must be), $C$ and $C'$ depend only on $d=\dim\alpha$, $c_M$, $c_A$ such that, with probability at least $1-C'/(nm)$,
--   $$h(\theta^*)\le C(K+L)^2(\delta')^2 .$$
--
--   Together with the selector property $h(\hat\theta)\le h(\theta^*)$ it gives Lemma 2.
--
--   **Formalization Note.** $h$ counts entries with $X_{ij}\le t$ and sums $t=0,\dots,T-1$, as (7) does; the display of $h$ in B.1.1 prints "$=t$". The p. 41 form of the sparsity condition is carried because the proof uses Lemma 15.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 43, Lemma 16

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_16 (d : ℕ) (cM cA : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ),
        IsBestRankApprox I.r svdr →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω |
          I.hobj (d + 1) svdr (I.obs ω) I.θstar ≤ C * (K + L) ^ 2 * I.δ' hI.r_pos μ L ^ 2} := by sorry

end InventoryAnomaly.EW
