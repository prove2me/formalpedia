-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_4_11
-- name    : LpBallVI.Affine.lemma_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:23.782575+00:00
-- url     : https://prove2.me/theorems/ecd94913-7f0c-4f91-a483-1035c667fb61
-- title:
--   Lemma 4.11 (Rubinstein 2018; Bernasconi et al. 2026) — LinVI over [0,1]^d is PPAD-hard at a constant accuracy
-- statement:
--   **LinVI** asks, for rational $D \in [-1,1]^{d\times d}$ with $\|D\|_1 \le 1$, $\|D\|_\infty \le 1$ and rational $b \in [-1,1]^d$, for $z \in [0,1]^d$ with $(Dz + b)_i(z'_i - z_i) \ge -\varepsilon$ for all $i$ and $z'_i \in [0,1]$. The cited result is that
--   $$\exists\, \varepsilon \in (0, 1] \text{ (an absolute constant)}:\quad \text{LinVI at accuracy } \varepsilon \text{ is PPAD-hard}.$$
--   It yields clause (ii) of Theorem 4.1 by an affine change of variables onto $B_\infty$.
--
--   Differences from the source:
--   - encoding: LinVI with ε ∈ (0,1] given in the input; 'even when ϵ > 0 is an absolute constant' → ∃ rational ε ∈ (0,1] such that LinVI(ε), the problem with that ε fixed and not encoded, is PPAD-hard; reason: restricting the inputs to one constant ε is the problem LinVI(ε)
--   - encoding: LinVI inputs and answers → codes encRatMatrix d D ++ encRatVec d b; answers rational z coded by encRatVec; reason: a concrete code of the search problem
--   - encoding: PPAD (search problems reducible to End-of-Line), PPAD-hard/-complete → QuasiStrictNE.PPAD / CEPolytopeHard.PPADHard / QuasiStrictNE.PPADComplete: total problems with a polynomial-time Levin search reduction to End-of-Line, hardness by such reductions from every PPAD problem; reason: the platform's published PPAD layer; no answer-length bound, as on p. 13
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 36, Lemma 4.11 and the definition of LinVI

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_LpBallVI_Affine_LinVI

namespace LpBallVI.Affine

/-- **Lemma 4.11** (Rubinstein 2018; Bernasconi et al. 2026), p. 36: `LinVI` is PPAD-hard even when
`ε > 0` is an absolute constant: for some constant `ε ∈ (0, 1]`, `LinVI` at accuracy `ε` is
PPAD-hard. -/
theorem lemma_4_11 :
    ∃ ε : ℚ, 0 < ε ∧ ε ≤ 1 ∧ CEPolytopeHard.PPADHard (LinVI (ε : ℝ)) := by sorry

end LpBallVI.Affine
