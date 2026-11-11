-- Prove2me | Theorems.Thm_LpBallVI_Affine_theorem_4_1
-- name    : LpBallVI.Affine.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:12:21.195203+00:00
-- url     : https://prove2.me/theorems/d14cfba3-c16d-413b-8d1a-1af639a8d2b8
-- title:
--   Theorem 4.1 — affine VIs on ℓp balls: PPAD-complete at accuracy d^(−c_p) for rational p ∈ [1,∞)∖{2}, and at a constant accuracy for p = ∞
-- statement:
--   For an exponent $p$ (rational, or $\infty$) and an accuracy function $\varepsilon(d)$, let **AffBallVI$(p, \varepsilon)$** be the search problem: given $d \ge 1$, $A \in \mathbb Q^{d\times d}$ and $b \in \mathbb Q^d$ with all coefficients in $[-1,1]$ such that $F(z) = Az + b$ is 1-Lipschitz on $B^d_p = \{\|x\|_p \le 1\}$, find a rational $x \in B^d_p$ with
--   $$\operatorname{Gap}_{B^d_p}(x;F) = \max_{x' \in B^d_p} \langle x' - x, Ax + b\rangle \le \varepsilon(d).$$
--   Then (i) for every rational $p \in [1, \infty) \setminus \{2\}$ there is $c_p > 0$ such that AffBallVI$(p, d \mapsto d^{-c_p})$ is PPAD-complete, and (ii) there is a constant $c \in (0,1)$ such that AffBallVI$(\infty, d \mapsto c)$ is PPAD-complete. For $p = 2$ the paper shows the opposite (polynomial time, Theorem 5.1): the geometry of the ball decides the complexity of affine VIs.
--
--   Differences from the source:
--   - reading: 1-Lipschitz-continuous operator (norm unnamed) → ‖F(x) − F(y)‖ ≤ ‖x − y‖ in the Euclidean norm for x, y ∈ B^d_p; reason: Appendix B works in the Euclidean norm; 'an unsubscripted norm denotes the Euclidean norm' (p. 12)
--   - reading: Ballp-VI 'for ϵ = d^{−c_p}' (resp. 'ϵ = c') → the accuracy is the fixed function ε(d) of the instance's dimension, not an input; reason: the accuracy is fixed by the theorem, not chosen by the input
--   - reading: (ii) a constant c > 0, with Ballp-VI's accuracy ϵ ∈ (0,1) → ∃ c with 0 < c < 1; reason: Ballp-VI takes ϵ ∈ (0,1)
--   - encoding: inputs A, b and answers x in binary → valid inputs encRatMatrix d A ++ encRatVec d b with d ≥ 1; answers rational x coded by encRatVec, no length bound; reason: a concrete code of the search problem
--   - encoding: ‖x‖_p for rational p; ‖x‖_∞ → (Σ|x_i|^p)^{1/p} with Real.rpow; ⨆_i |x_i|; reason: standard definitions
--   - encoding: Gap_K(x;F) = max_{x'∈K} ⟨x'−x, F(x)⟩ ≤ ε → ⟨x'−x, F(x)⟩ ≤ ε for every x' ∈ K; reason: K is a nonempty compact ball, so the maximum is attained and the two agree
--   - encoding: PPAD (search problems reducible to End-of-Line), PPAD-hard/-complete → QuasiStrictNE.PPAD / CEPolytopeHard.PPADHard / QuasiStrictNE.PPADComplete: total problems with a polynomial-time Levin search reduction to End-of-Line, hardness by such reductions from every PPAD problem; reason: the platform's published PPAD layer; no answer-length bound, as on p. 13
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 19, Theorem 4.1 (abridged as Theorem 1.1, p. 4; proof pp. 34–36)

import Mathlib
import Definitions.Def_QuasiStrictNE_PPADComplete
import Definitions.Def_LpBallVI_Affine_AffBallVI

namespace LpBallVI.Affine

/-- **Theorem 4.1**, p. 19 (abridged as Theorem 1.1, p. 4): for affine operators `F(z) = A z + b`
with rational coefficients in `[−1, 1]`, (i) for every rational `p ∈ [1, ∞) ∖ {2}` there is
`c_p > 0` such that `Ballp-VI` at accuracy `ε = d^{−c_p}` is PPAD-complete, and (ii) for `p = ∞`
there is a constant `c ∈ (0, 1)` such that `Ball∞-VI` at accuracy `ε = c` is PPAD-complete. -/
theorem theorem_4_1 :
    (∀ p : ℚ, 1 ≤ p → p ≠ 2 → ∃ c : ℝ, 0 < c ∧
      QuasiStrictNE.PPADComplete (AffBallVI (.fin p) (fun d => (d : ℝ) ^ (-c)))) ∧
    (∃ c : ℝ, 0 < c ∧ c < 1 ∧
      QuasiStrictNE.PPADComplete (AffBallVI .infty (fun _ => c))) := by sorry

end LpBallVI.Affine
