-- Prove2me | Theorems.Thm_LpBallVI_Affine_sec_4_3_1_p_one
-- name    : LpBallVI.Affine.sec_4_3_1_p_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:26.069568+00:00
-- url     : https://prove2.me/theorems/56e491ad-306c-4aa3-bf6b-8dedfa825791
-- title:
--   §4.3.1, case p = 1 (Chen–Deng–Teng 2009 + symmetrization) — inverse-polynomially approximate symmetric Nash equilibria of (A, Aᵀ) are PPAD-hard
-- statement:
--   For a rational $A \in [0,1]^{d\times d}$, an $\varepsilon$-approximate symmetric Nash equilibrium of $(A, A^\top)$ is $x \in \Delta_d$ with $\max_i (Ax)_i - x^\top A x \le \varepsilon$. The cited result (Chen, Deng and Teng 2009, with the symmetrization of Nisan, Roughgarden, Tardos and Vazirani 2007, Theorem 2.4) is that at inverse-polynomial accuracy the problem is PPAD-hard:
--   $$\exists\, c > 0:\quad \text{finding a } d^{-c}\text{-approximate symmetric Nash equilibrium of } (A, A^\top) \text{ is PPAD-hard}.$$
--   It yields clause (i) of Theorem 4.1 at $p = 1$.
--
--   Differences from the source:
--   - reading: inverse-polynomial accuracy → accuracy d^{−c} for some real c > 0, d the number of pure strategies; reason: the polynomial in the game size taken as a power of d
--   - encoding: symmetric games with rational A ∈ [0,1]^{d×d} → codes encRatMatrix d A (d ≥ 1); answers rational x coded by encRatVec; reason: a concrete code of the search problem
--   - encoding: PPAD (search problems reducible to End-of-Line), PPAD-hard/-complete → QuasiStrictNE.PPAD / CEPolytopeHard.PPADHard / QuasiStrictNE.PPADComplete: total problems with a polynomial-time Levin search reduction to End-of-Line, hardness by such reductions from every PPAD problem; reason: the platform's published PPAD layer; no answer-length bound, as on p. 13
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 36, §4.3.1, case p = 1

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_LpBallVI_Affine_SymNash

namespace LpBallVI.Affine

/-- **§4.3.1, case p = 1** (Chen–Deng–Teng 2009 with the symmetrization of Nisan–Roughgarden–Tardos–
Vazirani 2007, Theorem 2.4), p. 36: computing an inverse-polynomially approximate symmetric Nash
equilibrium of a symmetric bimatrix game `(A, Aᵀ)`, `A ∈ [0, 1]^{d×d}` rational, is PPAD-hard: for
some `c > 0`, accuracy `d^{−c}`. -/
theorem sec_4_3_1_p_one :
    ∃ c : ℝ, 0 < c ∧ CEPolytopeHard.PPADHard (SymNash (fun d => (d : ℝ) ^ (-c))) := by sorry

end LpBallVI.Affine
