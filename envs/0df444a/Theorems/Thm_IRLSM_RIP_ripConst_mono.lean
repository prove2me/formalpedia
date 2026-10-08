-- Prove2me | Theorems.Thm_IRLSM_RIP_ripConst_mono
-- name    : IRLSM.RIP.ripConst_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:46.456129+00:00
-- url     : https://prove2.me/theorems/497cd210-a28f-4930-962f-8b071e6cf2a7
-- title:
--   Proof of Proposition 6.8, p. 20 — δ_k ≤ δ_k' for k ≤ k' (so δ_3k ≤ δ_4k)
-- statement:
--   Let $\mathcal S : \mathbb R^{n\times p}\to\mathbb R^m$ be linear and $k \le k'$. Then the rank restricted isometry constants satisfy
--   $$
--   \delta_k(\mathcal S) \le \delta_{k'}(\mathcal S) .
--   $$
--
--   The proof of Proposition 6.8 uses the case $\delta_{3k} \le \delta_{4k}$ to conclude that $\eta < 1$.
--
--   **Formalization Note.** $\delta_k$ is the squared-form constant of Definition 1.1, defined for every $k \in \mathbb N$.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), proof of Proposition 6.8, p. 20 ("Since δ3k ≤ δ4k")

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.RIP

/-- The restricted isometry constants are nondecreasing in the rank bound:
`k ≤ k'` implies `δ_k ≤ δ_{k'}` (used as `δ_{3k} ≤ δ_{4k}`).

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, proof of Proposition 6.8, p. 20 ("Since δ_3k ≤ δ_4k").

Formalization Note: `ripConst` is the squared-form constant of Definition 1.1, defined for
every `k : ℕ`. -/
theorem ripConst_mono {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) {k k' : ℕ}
    (h : k ≤ k') : IRLSM.Convergence.ripConst A k ≤ IRLSM.Convergence.ripConst A k' := by sorry

end IRLSM.RIP
