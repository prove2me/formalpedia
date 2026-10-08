-- Prove2me | Theorems.Thm_MinRankRecovery_Recovery_eq_3_7
-- name    : MinRankRecovery.Recovery.eq_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:19.570823+00:00
-- url     : https://prove2.me/theorems/6b340889-d081-4c70-8397-5732e064cbfb
-- title:
--   (3.7) — ‖𝒜(R)‖ ≥ ((1 − δ_5r) − (9/11)(1 + δ_3r)) ‖R₀‖_F, positive when 9δ_3r + 11δ_5r < 2
-- statement:
--   Let $\mathcal A:\mathbb R^{m\times n}\to\mathbb R^p$ be a linear map with restricted isometry constants $\delta_r$, and let $r\ge1$. Let $R,R_0,R_1$ and $R_2,\dots,R_N$ be real $m\times n$ matrices such that
--   1. $R=R_0+R_1+\sum_{j\ge2}R_j$;
--   2. $\operatorname{rank}(R_0+R_1)\le5r$ and $\operatorname{rank}(R_j)\le3r$ for every $j\ge2$;
--   3. $\langle R_0,R_1\rangle=0$;
--   4. $\sum_{j\ge2}\|R_j\|_F\le\sqrt{2/3}\,\|R_0\|_F$.
--
--   Then
--   $$\|\mathcal A(R)\|\;\ge\;\Big((1-\delta_{5r})-\tfrac{9}{11}(1+\delta_{3r})\Big)\,\|R_0\|_F ,$$
--   and the factor $(1-\delta_{5r})-\tfrac{9}{11}(1+\delta_{3r})$ is strictly positive whenever $9\delta_{3r}+11\delta_{5r}<2$.
--
--   This is the final estimate of the proof of Theorem 3.3: applied to the error $R=X^*-X_0$, for which $\mathcal A(R)=0$, it forces $R_0=0$ once the factor is positive.
--
--   **Formalization Note** Item 4 is (3.6) after simplifying $\sqrt{2r}/\sqrt{3r}=\sqrt{2/3}$. Item 3 is used by the paper's third line of (3.7) ($\|R_0+R_1\|_F\ge\|R_0\|_F$) without being written; it is made an explicit hypothesis. The family $R_2,\dots,R_N$ is any finite family, indexed in Lean by `Fin N`. $\|\mathcal A(R)\|$ is `measNorm Xs R`, and $\delta_{3r},\delta_{5r}$ are `ripConst Xs (3*r)`, `ripConst Xs (5*r)`.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, §3, proof of Theorem 3.3, (3.7) and the sentence after it, p. 14

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core
import Definitions.Def_MinRankRecovery_Recovery_ripConst

open HighDimStat.MatrixRank Matrix

namespace MinRankRecovery.Recovery

/-- (3.7), p. 14, and the sentence after it: if `R = R₀ + R₁ + Σ_{j ≥ 2} R_j` with
`rank(R₀ + R₁) ≤ 5r`, `rank R_j ≤ 3r`, `⟨R₀, R₁⟩ = 0` and `Σ_{j ≥ 2} ‖R_j‖_F ≤ √(2/3) ‖R₀‖_F`, then
`‖𝒜(R)‖ ≥ ((1 - δ_5r) - (9/11)(1 + δ_3r)) ‖R₀‖_F`; and that factor is positive when
`9 δ_3r + 11 δ_5r < 2`. -/
theorem eq_3_7 {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) (r : ℕ) (hr : 1 ≤ r)
    (R R0 R1 : Matrix (Fin m) (Fin n) ℝ) {N : ℕ} (Rt : Fin N → Matrix (Fin m) (Fin n) ℝ)
    (hR : R = R0 + R1 + ∑ j, Rt j) (hrank01 : (R0 + R1).rank ≤ 5 * r)
    (hrankt : ∀ j, (Rt j).rank ≤ 3 * r) (horth : traceInner R0 R1 = 0)
    (htail : ∑ j, frobeniusNorm (Rt j) ≤ Real.sqrt (2 / 3) * frobeniusNorm R0) :
    ((1 - ripConst Xs (5 * r)) - 9 / 11 * (1 + ripConst Xs (3 * r))) * frobeniusNorm R0 ≤
        measNorm Xs R ∧
      (9 * ripConst Xs (3 * r) + 11 * ripConst Xs (5 * r) < 2 →
        0 < (1 - ripConst Xs (5 * r)) - 9 / 11 * (1 + ripConst Xs (3 * r))) := by sorry

end MinRankRecovery.Recovery
