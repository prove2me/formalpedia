-- Prove2me | Theorems.Thm_LpBallVI_Affine_theorem_B_1
-- name    : LpBallVI.Affine.theorem_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:12:12.001266+00:00
-- url     : https://prove2.me/theorems/cdd66440-c817-4312-8acb-e06f62a05fea
-- title:
--   Theorem B.1 — circuit Ballp-VI is in PPAD for every fixed rational p ≥ 1 and for p = ∞
-- statement:
--   Let $p \ge 1$ be a fixed rational, or $p = \infty$. Consider Ballp-VI with operators $F : B^d_p \to \mathbb R^d$ given by well-behaved arithmetic circuits over rational constants and $\{+, -, \times, \min, \max\}$ that are 1-Lipschitz, and a rational accuracy $\varepsilon \in (0,1)$ in binary; an answer is a rational $x \in B^d_p$ with $\max_{x' \in B^d_p}\langle x' - x, F(x)\rangle \le \varepsilon$. Then
--   $$\text{Ballp-VI} \in \mathrm{PPAD}.$$
--   This is the membership half of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: well-behaved arithmetic circuit over rational constants and {+, −, ×, min, max} → NadlerCLS.Circ with Circ.Valid C d d and no ArithmeticGate.test gate; reason: the platform's published circuit model minus its comparison gate
--   - reading: 1-Lipschitz (norm unnamed) → 1-Lipschitz on B^d_p in the Euclidean norm; reason: Appendix B's proof works in the Euclidean norm
--   - encoding: inputs and answers in binary → encBin d ++ encCirc C ++ encRat ε; answers rational x coded by encRatVec; reason: a concrete code of the search problem
--   - encoding: Gap_K(x;F) = max_{x'∈K} ⟨x'−x, F(x)⟩ ≤ ε → ⟨x'−x, F(x)⟩ ≤ ε for every x' ∈ K; reason: K is a nonempty compact ball, so the maximum is attained and the two agree
--   - encoding: PPAD (search problems reducible to End-of-Line), PPAD-hard/-complete → QuasiStrictNE.PPAD / CEPolytopeHard.PPADHard / QuasiStrictNE.PPADComplete: total problems with a polynomial-time Levin search reduction to End-of-Line, hardness by such reductions from every PPAD problem; reason: the platform's published PPAD layer; no answer-length bound, as on p. 13
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 50, Theorem B.1

import Mathlib
import Definitions.Def_QuasiStrictNE_PPAD
import Definitions.Def_LpBallVI_Affine_CircBallVI

namespace LpBallVI.Affine

/-- **Theorem B.1**, p. 50: for every fixed rational `p ≥ 1`, and also for `p = ∞`, `Ballp-VI`
belongs to PPAD, for 1-Lipschitz operators represented by well-behaved arithmetic circuits and every
rational `ε ∈ (0, 1)` encoded in binary. -/
theorem theorem_B_1 :
    (∀ p : ℚ, 1 ≤ p → CircBallVI (.fin p) ∈ QuasiStrictNE.PPAD) ∧
      CircBallVI .infty ∈ QuasiStrictNE.PPAD := by sorry

end LpBallVI.Affine
