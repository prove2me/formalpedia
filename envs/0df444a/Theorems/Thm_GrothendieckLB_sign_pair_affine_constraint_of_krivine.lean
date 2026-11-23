-- Prove2me | Theorems.Thm_GrothendieckLB_sign_pair_affine_constraint_of_krivine
-- name    : GrothendieckLB.sign_pair_affine_constraint_of_krivine
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:00:59.673808+00:00
-- url     : https://prove2.me/theorems/c8bc4b3a-2603-4dff-b437-556996c44a06
-- title:
--   The ordinary-scheme affine strip extends to every measurable sign pair
-- statement:
--   Fix $\lambda\in\mathbb R$ and suppose every ordinary Krivine scheme, in every dimension, satisfies
--   $$
--   b_3\ge(1+\lambda)b_1-\Bigl(\lambda+\frac56\Bigr).
--   $$
--   Then every measurable sign pair $f,g:\mathbb R^d\to\{\pm1\}$, whether odd or not, satisfies the same inequality for $b_1=[t]H_{f,g}$ and $b_3=[t^3]H_{f,g}$:
--   $$
--   [t^3]H_{f,g}\ge(1+\lambda)[t]H_{f,g}-\Bigl(\lambda+\frac56\Bigr).
--   $$
--   Only the odd Hermite components enter degrees one and three. One may independently randomize odd sign extensions of $f$ and $g$ on the antipodal pairs $\{x,-x\}$, choosing their means to be the odd parts $(f(x)-f(-x))/2$ and $(g(x)-g(-x))/2$. Averaging the assumed inequality over these ordinary Krivine schemes gives the stated bare-pair inequality. This supplies the non-odd case required by Definition 10.1 without incorrectly asserting that a single non-odd pair is itself a Krivine scheme.
--
--   **Formalization Note** The randomized oddification is part of the proof obligation of this lemma, not an additional hypothesis. The coefficient convention is $b_1=H'(0)$ and $b_3=H^{(3)}(0)/6$.
-- source:
--   Saha, Li, Xue, Chaudhuri, Klivans, Kothari, Meka, New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158, Section 7 odd Hermite coefficients p.31; Section 9 introductory paragraph p.41; mixed sign pairs in Definition 10.1 p.42 and preservation step in the lower-bound proof p.43. General affine slope as assumed here: Li et al., arXiv:2608.11195v3, Appendix A, pp.16-17.

import Mathlib
import Definitions.Def_GrothendieckLB_IsLimitingMixed

namespace GrothendieckLB

/-- If an affine coefficient strip holds for every ordinary Krivine scheme, then it also holds for every measurable sign pair, with no oddness hypothesis. -/

theorem sign_pair_affine_constraint_of_krivine (lam : ℝ)
    (hcon : ∀ (k : ℕ) (S : GrothendieckConstant.KrivineScheme k),
      (1 + lam) * GrothendieckConstant.coeffLinear S - (lam + 5 / 6) ≤
        GrothendieckConstant.coeffCubic S)
    {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g) :
    (1 + lam) * taylorCoeff 1 (pairCorr f g) - (lam + 5 / 6) ≤
      taylorCoeff 3 (pairCorr f g) := by sorry
