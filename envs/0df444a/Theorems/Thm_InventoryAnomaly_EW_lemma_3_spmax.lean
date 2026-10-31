-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_3_spmax
-- name    : InventoryAnomaly.EW.lemma_3_spmax
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T08:57:22.960856+00:00
-- url     : https://prove2.me/theorems/df8cb6d4-7f4e-4541-bb1f-241aa4e0d57e
-- title:
--   Lemma 3, p. 23 (sparsity as read on p. 41; universal constant in place of 2) — |f*_ij − f̂_ij| ≤ min(Cδ/(x*_ij + y*_ij), 1) on Ω
-- statement:
--   Throughout, the standing assumptions of §2 (pp. 8–10) are in force (as in the `InventoryAnomaly_EW_Model` definition: $2\le m\le n$, rank-$r$ SVD $M^*=U\Sigma V^\top$ with condition number $\kappa$, $c_M\le\|M^*\|_{\max}\le L$, $\mu$-incoherence, the sparsity condition $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$, $p_A^*\le 1-c_A$, and the three assumptions on $\mathrm{Anom}(\cdot,\cdot)$ with constants $K,L$). In addition we assume the sparsity condition **in the form in which the proof of Theorem 2 reads it** (p. 41): for the maximal entry $\|M^*\|_{\max}$,
--   $$\sqrt{p_O}\ \ge\ C_{sp}\,\frac{\log^{1.5}(m)\,\mu r L\kappa^2}{\|M^*\|_{\max}\sqrt m}.$$
--   The paper derives this from §2 ("By the assumption in Section 2"), which is only valid when $L/\|M^*\|_{\max}$ is bounded; the milestone Theorem 2 is formalized with this hypothesis (`SparsityMax`), so every result that rests on Theorem 2 must carry it too.
--
--   Assume Lemma 1's regularity conditions (constant $C_{RC}$), let $\mathrm{SVD}_r$ be a best rank-$r$ approximation and $\hat\theta\in\Theta$ any estimator with $h(\hat\theta)\le h(\theta^*)$. Let $\delta=(K+L)^3\kappa^4\mu rL^2\sqrt{\log m/(p_Om)}$, let $f^*_{ij}=y^*_{ij}/(x^*_{ij}+y^*_{ij})$ (8) and $\hat f_{ij}=\hat y_{ij}/(\hat x_{ij}+\hat y_{ij})$ (9). There are constants $C_{sp},C,C'>0$ depending only on $d,c_M,c_A,C_{RC}$ such that, with probability at least $1-C'/(nm)$, for every $(i,j)\in\Omega$,
--   $$|f^*_{ij}-\hat f_{ij}|\le\min\Big(\frac{C\delta}{x^*_{ij}+y^*_{ij}},\,1\Big).$$
--
--   (The paper states the constant $2$; as in the milestone formalization, a universal constant $C$ is used.) The paper's proof (p. 47) is a corollary of Lemmas 18 and 19.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 23, Lemma 3; proof p. 47 (corollary of Lemmas 18 and 19); sparsity assumption as read in the proof of Theorem 2, p. 41

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_3_spmax (d : ℕ) (cM cA CRC : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1)
    (hCRC : 0 < CRC) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        I.Regular hI.r_pos cA CRC K L μ →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω | ∀ ij ∈ I.omega (I.obs ω),
          |I.fstar (I.obs ω) ij.1 ij.2 - I.fhat svdr θhat (I.obs ω) ij.1 ij.2| ≤
            min (C * ((K + L) ^ 3 * L * I.δ' hI.r_pos μ L) /
              (I.xstar (I.obs ω) ij.1 ij.2 + I.ystar (I.obs ω) ij.1 ij.2)) 1} := by sorry

end InventoryAnomaly.EW
