-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_1_spmax
-- name    : InventoryAnomaly.EW.lemma_1_spmax
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T08:57:34.050625+00:00
-- url     : https://prove2.me/theorems/8147812a-29f8-48bb-be16-76e19324b78f
-- title:
--   Lemma 1, p. 17 (sparsity as read on p. 41) — ‖θ̂ − θ*‖ ≤ C(K + L)δ′ w.p. 1 − O(1/nm)
-- statement:
--   Throughout, the standing assumptions of §2 (pp. 8–10) are in force (as in the `InventoryAnomaly_EW_Model` definition: $2\le m\le n$, rank-$r$ SVD $M^*=U\Sigma V^\top$ with condition number $\kappa$, $c_M\le\|M^*\|_{\max}\le L$, $\mu$-incoherence, the sparsity condition $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$, $p_A^*\le 1-c_A$, and the three assumptions on $\mathrm{Anom}(\cdot,\cdot)$ with constants $K,L$). In addition we assume the sparsity condition **in the form in which the proof of Theorem 2 reads it** (p. 41): for the maximal entry $\|M^*\|_{\max}$,
--   $$\sqrt{p_O}\ \ge\ C_{sp}\,\frac{\log^{1.5}(m)\,\mu r L\kappa^2}{\|M^*\|_{\max}\sqrt m}.$$
--   The paper derives this from §2 ("By the assumption in Section 2"), which is only valid when $L/\|M^*\|_{\max}$ is bounded; the milestone Theorem 2 is formalized with this hypothesis (`SparsityMax`), so every result that rests on Theorem 2 must carry it too.
--
--   Assume Lemma 1's regularity conditions on $F(\theta)=(g_t(\theta,M^*e(\theta^*)/e(\theta)))_{t\le d}$ with constant $C_{RC}$: $F$ is $C^1$ and injective on $\Theta$, $B_{\tilde\delta}(\theta^*)\subset\Theta$ with $\tilde\delta=\delta'(K+L)\log m$, $\|J_F(\theta)-J_F(\theta^*)\|_2\le (C_{RC}/\tilde\delta)\|\theta-\theta^*\|$ on that ball, and $\|J_F(\theta^*)^{-1}\|_2\le C_{RC}$. Let $\mathrm{SVD}_r$ be any best rank-$r$ approximation and $\hat\theta\in\Theta$ any moment-matching estimate with $h(\hat\theta)\le h(\theta^*)$ (objective (7)). Then there are constants $C_{sp},C,C'>0$ depending only on $d,c_M,c_A,C_{RC}$ such that, with probability at least $1-C'/(nm)$,
--   $$\|\hat\theta-\theta^*\|\le C(K+L)\,\kappa^4\mu rL\sqrt{\frac{\log m}{p_Om}}\qquad\text{(Eq. (6))}.$$
--
--   The paper's proof (p. 44, "Proof of Lemma 1") combines Lemma 2 with the inverse-function bound Lemma 17.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 17, Lemma 1 and Eq. (6) p. 16; proof p. 44 (Proof of Lemma 1); sparsity assumption as read in the proof of Theorem 2, p. 41

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_1_spmax (d : ℕ) (cM cA CRC : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1)
    (hCRC : 0 < CRC) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        I.Regular hI.r_pos cA CRC K L μ →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω |
          ‖θhat (I.obs ω) - I.θstar‖ ≤ C * (K + L) * I.δ' hI.r_pos μ L} := by sorry

end InventoryAnomaly.EW
