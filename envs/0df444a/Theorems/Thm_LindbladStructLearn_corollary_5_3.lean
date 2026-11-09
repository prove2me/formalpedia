-- Prove2me | Theorems.Thm_LindbladStructLearn_corollary_5_3
-- name    : LindbladStructLearn.corollary_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:03:04.341632+00:00
-- url     : https://prove2.me/theorems/f32b4596-a3a6-43ba-8a5a-95330eb01863
-- title:
--   Corollary 5.3 — $\|\mathcal F(x) - A\Delta\|_{B_1} \le ct\|\Delta\|_{B_1}$ with $c = (23k)!\,2g$
-- statement:
--   Let $1 < k \le n$ and $g > 0$. Let $\lambda$ and $x$ be vectors on the $k$-local pairs with $\|\lambda\|_{B_1} \le g$ and $\|x\|_{B_1} \le g$, and put $\Delta = x - \lambda$. Let $0 < t < 1/(8ekg)$, $A = A_k$ and $\mathcal F(x) = E(x)/t - E(\lambda)/t$. Then
--
--   $$\big\|\mathcal F(x) - A\Delta\big\|_{B_1} \le c\,t\,\|\Delta\|_{B_1}, \qquad c = (23k)!\,2g.$$
--
--   The corollary bounds the error of the linearized update used by Algorithm 4. The hypotheses $k > 1$ and $g > 0$ are the standing assumptions of Section 5 (p.32).
--
--   Differences from the source:
--   - generalization: λ the true parameters of the unknown Lindbladian (Section 5) → λ any vector on the k-local pairs with ‖λ‖_B1 ≤ g; reason: the proof uses only ‖λ‖_B1 ≤ g and Lemma 4.1, which holds for any vector; the true parameters are a special case
--   - encoding: t < 1/(8ekg) → 0 < t < 1/(8ekg); reason: F divides by t, so t > 0 is implicit
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Corollary 5.3, Eq. (5.17), p.35

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_Fvec
import Definitions.Def_LindbladStructLearn_Amat
import Definitions.Def_LindbladStructLearn_ext
import Definitions.Def_LindbladStructLearn_b1Norm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Corollary 5.3 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (5.17), p.35): let `‖x‖_B1 ≤ g`, `Δ = x − λ` and `t < 1/(8ekg)`,
and let `A = A_k`. Then `‖F(x) − AΔ‖_B1 ≤ c t ‖Δ‖_B1` for `c = (23k)! 2g`, where
`F(x) = E(x)/t − E(λ)/t` (Eq. (5.7)).

**Formalization Note** `λ` is the true parameter vector of Section 5 (`k`-local, `‖λ‖_B1 ≤ g`),
here any vector on the index set with `‖λ‖_B1 ≤ g`. Section 5's standing assumptions `k > 1` and
`g > 0` (p.32) are hypotheses; `t > 0` (`F` divides by `t`); `k ≤ n` (Notation 3.2). -/
theorem corollary_5_3 (n k : ℕ) (hk : 1 < k) (hkn : k ≤ n) (g : ℝ) (hg : 0 < g)
    (lam x : Idx n k → ℂ) (hlam : b1Norm (ext lam) ≤ g) (hx : b1Norm (ext x) ≤ g)
    (t : ℝ) (ht : 0 < t) (ht' : t < 1 / (8 * Real.exp 1 * k * g)) :
    b1Norm (ext (Fvec t lam x - Matrix.mulVec (Amat n k) (x - lam))) ≤
      (((23 * k).factorial : ℝ) * 2 * g) * t * b1Norm (ext (x - lam)) := by sorry

end LindbladStructLearn
