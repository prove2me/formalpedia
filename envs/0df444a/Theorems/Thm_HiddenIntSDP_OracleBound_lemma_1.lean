-- Prove2me | Theorems.Thm_HiddenIntSDP_OracleBound_lemma_1
-- name    : HiddenIntSDP.OracleBound.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:52.382987+00:00
-- url     : https://prove2.me/theorems/b270ece5-ed14-49e8-923a-813b08dca894
-- title:
--   Lemma 1, p. 19 — β representation of the mixed signal
-- statement:
--   Let $\ell=n/k$, $\kappa=1/8$, $\beta_{ja}=\langle\mu_a-\mu_{\sigma^*(j)},g_j\rangle-\kappa\|\mu_{\sigma^*(j)}-\mu_a\|_2^2$, and $\widehat X_{ja}=\ell^{-1}\sum_{i\in C_a^*}(Y-Y^*)_{ji}$. For every feasible SDP matrix $Y$,
--
--   $$
--   \frac1\ell\left(S_3+\frac14S_4\right)
--   =\sum_j\sum_{a\ne\sigma^*(j)}\beta_{ja}\widehat X_{ja}.
--   $$
--
--   This identity turns the remaining deterministic part of the SDP argument into a linear objective in the averaged error entries.
-- source:
--   Fei & Chen, Hidden integrality and semi-random robustness of SDP relaxation for sub-Gaussian mixture model, arXiv:1803.06510v2, p. 19, Lemma 1, (18)–(19)

import Definitions.Def_HiddenIntSDP_OracleBound_Proof

namespace HiddenIntSDP.OracleBound

/-- Fei–Chen, Lemma 1, equation (19), p. 19. -/
theorem lemma_1 {n k d : ℕ} (hn : 4 ≤ n) (hk : 2 ≤ k)
    (mu : Fin k → EuclideanSpace ℝ (Fin d)) (sig : Fin n → Fin k)
    (hbal : Balanced n k sig) (g : Fin n → EuclideanSpace ℝ (Fin d))
    (Y : Matrix (Fin n) (Fin n) ℝ) (hY : SDPFeasible n k Y) :
    (1 / ell n k) * (S3 mu sig g Y + (1 / 4 : ℝ) * S4 mu sig Y) =
      ∑ j, ∑ a ∈ Finset.univ.filter (fun a => a ≠ sig j),
        beta mu sig g j a * Xhat sig Y j a := by sorry

end HiddenIntSDP.OracleBound
