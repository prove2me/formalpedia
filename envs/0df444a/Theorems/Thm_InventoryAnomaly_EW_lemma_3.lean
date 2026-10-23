-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_3
-- name    : InventoryAnomaly.EW.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:56.602012+00:00
-- url     : https://prove2.me/theorems/52ded717-2cf0-4cd8-8274-9b115fc6193f
-- title:
--   Lemma 3, p. 23 (universal constant in place of 2) — w.p. 1 − O(1/nm), |f*_ij − f̂_ij| ≤ min(Cδ/(x*_ij + y*_ij), 1) for every (i, j) ∈ Ω
-- statement:
--   Throughout, the standing assumptions of §2 (pp. 8–10) are in force: $2\le m\le n$; $M^*\in\mathbb R_+^{n\times m}$ has rank $r\ge 1$ with SVD $M^*=U\Sigma V^\top$, singular values $\sigma_1^*\ge\dots\ge\sigma_r^*>0$ and condition number $\kappa=\sigma_1^*/\sigma_r^*$; $\|M^*\|_{\max}\ge c_M$ and $\|M^*\|_{\max}\le L$; $\|U\|_{2,\infty}\le\sqrt{\mu r/n}$, $\|V\|_{2,\infty}\le\sqrt{\mu r/m}$; the sparsity condition $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$; $p_A^*\le 1-c_A$; $\alpha^*\in\Gamma$; $\|\mathrm{Anom}(\alpha^*,M^*_{ij})\|_{\psi_1}\le L$; $k\mapsto\mathbb P(\mathrm{Anom}(\alpha,M)=k)$ is $K$-Lipschitz in $(\alpha,M)\in\Gamma\times[0,\infty)$; and $\mathbb E\,\mathrm{Anom}(\alpha,M)=g(\alpha)M$ with $g:\mathbb R^d\to[0,1]$ $K$-Lipschitz.
--
--   Assume Lemma 1's regularity conditions (constant $C_{RC}$), let $\mathrm{SVD}_r$ be a best rank-$r$ approximation and $\hat\theta\in\Theta$ any estimator with $h(\hat\theta)\le h(\theta^*)$. Let
--   $$\delta=(K+L)^3\kappa^4\mu rL^2\sqrt{\frac{\log m}{p_Om}} .$$
--   The constants $C_{sp}$ (how large the sparsity constant must be), $C$ and $C'$ depend only on $d=\dim\alpha$, $c_M$, $c_A$ and $C_{RC}$ such that, with probability at least $1-C'/(nm)$, for every $(i,j)\in\Omega$,
--   $$\big|f^*_{ij}-\hat f_{ij}\big|\le\min\Big(\frac{C\delta}{x^*_{ij}+y^*_{ij}},\ 1\Big).$$
--
--   This is Step 3 of the proof of Theorem 1: the plug-in posterior $\hat f$ is close to the Bayes posterior $f^*$.
--
--   **Formalization Note.** The paper prints $2\delta$; its proof combines Lemma 18, whose constant is unspecified, with Lemma 19, so the factor is read as a constant $C$. In Lean $\delta=(K+L)^3L\,\delta'$ with $\delta'$ of p. 17. On the null event $x^*_{ij}+y^*_{ij}=0$ the left side of the minimum is Lean's $0$.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 23, Lemma 3; proof pp. 45–47

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_3 (d : ℕ) (cM cA CRC : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1)
    (hCRC : 0 < CRC) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.Regular hI.r_pos cA CRC K L μ →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω | ∀ ij ∈ I.omega (I.obs ω),
          |I.fstar (I.obs ω) ij.1 ij.2 - I.fhat svdr θhat (I.obs ω) ij.1 ij.2| ≤
            min (C * ((K + L) ^ 3 * L * I.δ' hI.r_pos μ L) /
              (I.xstar (I.obs ω) ij.1 ij.2 + I.ystar (I.obs ω) ij.1 ij.2)) 1} := by sorry

end InventoryAnomaly.EW
