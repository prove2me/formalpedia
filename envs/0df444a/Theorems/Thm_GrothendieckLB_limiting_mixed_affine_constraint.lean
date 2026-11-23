-- Prove2me | Theorems.Thm_GrothendieckLB_limiting_mixed_affine_constraint
-- name    : GrothendieckLB.limiting_mixed_affine_constraint
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:21:20.541547+00:00
-- url     : https://prove2.me/theorems/9ff3d3f1-dc31-49f1-9dcc-4c0fe7327877
-- title:
--   Affine coefficient strips and $b_1\le1$ persist for limiting mixed schemes
-- statement:
--   Fix $\lambda\in\mathbb R$ and suppose that every ordinary Krivine scheme, in every dimension, satisfies
--
--   $$b_3\ge(1+\lambda)b_1-\Bigl(\lambda+\frac56\Bigr).$$
--
--   Then every limiting mixed correlation function $H$ satisfies the same inequality and also $[t]H\le1$.
--
--   The two leading coefficients are linear in the correlation function. The affine strip is preserved by averaging over a mixed rounding scheme and then by the coefficientwise limits in Definition 10.1. The upper bound on the linear coefficient is the normalized linear-mass estimate $|b_1(f,g)|\le(\pi/2)(2/\pi)=1$, which likewise survives mixing and coefficientwise limits. This is precisely the preservation step used on p.43 before applying the inverse-majorant barrier.
-- source:
--   Saha, Li, Xue, Chaudhuri, Klivans, Kothari, Meka, New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158, Section 9 introductory paragraph, p.41; Definition 10.1, p.42; Proof of lower bound, p.43. General slope: Li et al., arXiv:2608.11195v3, Appendix A, pp.16-17.

import Mathlib
import Definitions.Def_KrivineSchemeDefs
import Definitions.Def_GrothendieckLB_IsLimitingMixed
import Definitions.Def_GrothendieckLB_taylorCoeff

namespace GrothendieckLB

/-- A coefficient strip valid for all ordinary Krivine schemes, together with the linear-mass bound, persists for every limiting mixed correlation function. -/
theorem limiting_mixed_affine_constraint (lam : ℝ)
    (hcon : ∀ (k : ℕ) (S : GrothendieckConstant.KrivineScheme k),
      (1 + lam) * GrothendieckConstant.coeffLinear S - (lam + 5 / 6) ≤
        GrothendieckConstant.coeffCubic S)
    (H : ℝ → ℝ) (hH : IsLimitingMixed H) :
    (1 + lam) * taylorCoeff 1 H - (lam + 5 / 6) ≤ taylorCoeff 3 H ∧
      taylorCoeff 1 H ≤ 1 := by sorry
