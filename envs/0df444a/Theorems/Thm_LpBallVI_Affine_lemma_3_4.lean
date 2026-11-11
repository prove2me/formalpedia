-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_3_4
-- name    : LpBallVI.Affine.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:10.959971+00:00
-- url     : https://prove2.me/theorems/2d356c5b-9033-4156-a37b-70864a553e8e
-- title:
--   Lemma 3.4 — an ε-approximate VI solution is near S_R(F(z)), and F(z) is near λJ_p(z)
-- statement:
--   Let $1 < p < \infty$, $q = p/(p-1)$, $R > 0$, $F : \mathbb R^d \to \mathbb R^d$, and $z \in B_p(R)$ with $\operatorname{Gap}_{B_p(R)}(z;F) \le \varepsilon$ and $F(z) \ne 0$. With $r_p, \mu_p, C_p$ from (8) and $\theta_p = \min\{1, p-1\}$,
--   $$\|z - S_R(F(z))\|_p \le R\Big(\frac{\varepsilon}{\mu_p R \|F(z)\|_q}\Big)^{1/r_p},$$
--   and for some $\lambda > 0$,
--   $$\|F(z) - \lambda J_p(z)\|_q \le C_p \|F(z)\|_q \Big(\frac{\varepsilon}{\mu_p R \|F(z)\|_q}\Big)^{\theta_p/r_p}.$$
--   This is the quantitative form of the exact characterization: approximate solutions are close to the support point.
--
--   Differences from the source:
--   - encoding: ℝ^d → functions on a finite index type ι; reason: relabelling of coordinates; same instances
--   - encoding: Gap_K(x;F) = max_{x'∈K} ⟨x'−x, F(x)⟩ ≤ ε → ⟨x'−x, F(x)⟩ ≤ ε for every x' ∈ K; reason: K is a nonempty compact ball, so the maximum is attained and the two agree
--   - generalization: F : B^d_p(R) → ℝ^d continuous (Definition 2.1) → any map F : ℝ^ι → ℝ^ι; reason: only the value F(z) enters the statement; a continuous F on the ball extends to such a map
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 16, Lemma 3.4, (9), (10); constants (8)

import Mathlib
import Definitions.Def_LpBallVI_Affine_Geometry

namespace LpBallVI.Affine

/-- **Lemma 3.4**, p. 16: for `1 < p < ∞`, `z ∈ B_p(R)` with `Gap_{B_p(R)}(z; F) ≤ ε` and `F(z) ≠ 0`,
(9) `‖z − S_R(F(z))‖_p ≤ R (ε / (µ_p R ‖F(z)‖_q))^{1/r_p}`, and (10) for some `λ > 0`,
`‖F(z) − λ J_p(z)‖_q ≤ C_p ‖F(z)‖_q (ε / (µ_p R ‖F(z)‖_q))^{θ_p/r_p}`. -/
theorem lemma_3_4 {ι : Type*} [Fintype ι] (p R ε : ℝ) (hp : 1 < p) (hR : 0 < R)
    (F : (ι → ℝ) → ι → ℝ) (z : ι → ℝ) (hz : z ∈ ball p R) (hgap : GapLE (ball p R) F z ε)
    (hF : F z ≠ 0) :
    lpNorm p (z - supportPt p R (F z)) ≤
        R * (ε / (muP p * R * lpNorm (dualExp p) (F z))) ^ (1 / rP p) ∧
      ∃ lam : ℝ, 0 < lam ∧
        lpNorm (dualExp p) (F z - lam • dualityMap p z) ≤
          CP p * lpNorm (dualExp p) (F z) *
            (ε / (muP p * R * lpNorm (dualExp p) (F z))) ^ (thetaP p / rP p) := by sorry

end LpBallVI.Affine
