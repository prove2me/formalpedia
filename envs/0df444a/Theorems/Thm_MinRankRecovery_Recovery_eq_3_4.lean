-- Prove2me | Theorems.Thm_MinRankRecovery_Recovery_eq_3_4
-- name    : MinRankRecovery.Recovery.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:24.317996+00:00
-- url     : https://prove2.me/theorems/a915d1a2-8a8f-4a1f-89f6-882738dc921e
-- title:
--   (3.3)–(3.4) — the cone condition ‖R_c‖_* ≤ ‖R₀‖_*
-- statement:
--   Let $X_0,R,R_0,R_c$ be real $m\times n$ matrices with $R=R_0+R_c$, and suppose
--   $$X_0R_c^{\top}=0,\qquad X_0^{\top}R_c=0,\qquad \|X_0+R\|_*\le\|X_0\|_* .$$
--   Then
--   $$\|R_c\|_*\le\|R_0\|_* .$$
--
--   In the proof of Theorem 3.3, $R=X^*-X_0$ is the error of a nuclear-norm minimizer $X^*$ (so $\|X_0+R\|_*=\|X^*\|_*\le\|X_0\|_*$), and $R=R_0+R_c$ is the split of Lemma 3.4. The conclusion says the part of the error that is "orthogonal" to $X_0$ is controlled in nuclear norm by the low-rank part, the matrix analogue of the cone condition of $\ell_1$ recovery.
--
--   **Formalization Note** The paper's chain (3.3) is $\|X_0\|_*\ge\|X_0+R\|_*\ge\|X_0+R_c\|_*-\|R_0\|_*=\|X_0\|_*+\|R_c\|_*-\|R_0\|_*$; the statement keeps exactly its hypotheses (optimality, the decomposition, and the orthogonality conditions of Lemma 3.4 item 3) and its conclusion (3.4). The rank bound on $R_0$ is not used in this step and is omitted.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, §3, proof of Theorem 3.3, (3.3)–(3.4), p. 13

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

open HighDimStat.MatrixRank Matrix

namespace MinRankRecovery.Recovery

/-- (3.3)–(3.4), p. 13: if `R = R₀ + R_c`, `X₀ R_cᵀ = 0`, `X₀ᵀ R_c = 0` and
`‖X₀ + R‖_* ≤ ‖X₀‖_*`, then `‖R_c‖_* ≤ ‖R₀‖_*`. -/
theorem eq_3_4 {m n : ℕ} (X0 R R0 Rc : Matrix (Fin m) (Fin n) ℝ) (hR : R = R0 + Rc)
    (h1 : X0 * Rcᵀ = 0) (h2 : X0ᵀ * Rc = 0)
    (hopt : nuclearNorm (X0 + R) ≤ nuclearNorm X0) :
    nuclearNorm Rc ≤ nuclearNorm R0 := by sorry

end MinRankRecovery.Recovery
