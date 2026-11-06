-- Prove2me | Theorems.Thm_NondualOpt_proposition_28
-- name    : NondualOpt.proposition_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:00:40.681214+00:00
-- url     : https://prove2.me/theorems/686f2103-5fcc-43d5-b039-8a68094439e2
-- title:
--   Proposition 28 — uniform convexity vs covering
-- statement:
--   Let $1<r<\infty$, $p,q\ge1$, and suppose $B_{q^*}^d\subseteq L\,B_{r^*}^d$. Then for every $\alpha>0$
--   $$
--   \mathrm{sfat}_\alpha(L^d_{p,q^*})\lesssim_r\inf_{R>0}\Big[\Big(\frac{LR}\alpha\Big)^{\max\{2,r\}}+\log N\big(B_p^d,R\,B_r^d\big)\Big].
--   $$
--   Covering $B_p^d$ by translated $\ell_r$ balls of radius $R$ and bounding each local class by Lemma 26 and the union by Lemma 27 trades the radius against the covering number.
--
--   Differences from the source:
--   - encoding: ≲_r inf_{R>0} → a constant C depending only on r, chosen before d, p, q, L, α, with the bound for every R > 0; reason: definition of ≲_r and of the infimum
--   - encoding: B_{q∗}^d ⊆ L B_{r∗}^d; d ∈ ℕ; α → ‖g‖_{r∗} ≤ L whenever ‖g‖_{q∗} ≤ 1, with conjugate exponents as arguments; d ≥ 1; α > 0; values in [0, ∞]; reason: same statement
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Proposition 28, p.39

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM
import Definitions.Def_NondualOpt_linClassLp
import Definitions.Def_NondualOpt_sfat
import Definitions.Def_NondualOpt_coverNum
import Definitions.Def_NondualOpt_logN

open scoped ENNReal

namespace NondualOpt

/-- **Proposition 28 (Uniform convexity vs covering).** Let `1 < r < ∞` and suppose
`B_{q∗}^d ⊆ L B_{r∗}^d`. Then
`sfat_α(L^d_{p,q∗}) ≲_r inf_{R > 0} [(LR/α)^{max{2,r}} + log N(B_p^d, R B_r^d)]`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Proposition 28, p.39.

**Formalization Note.** `≲_r inf_R` is: a constant `C` depending only on `r`, chosen before
`d, p, q, L, α`, with the bound for every `R > 0`. `qs`, `rs` are the conjugate exponents `q∗, r∗`.
The inclusion `B_{q∗}^d ⊆ L B_{r∗}^d` is `‖g‖_{r∗} ≤ L` whenever `‖g‖_{q∗} ≤ 1`. `α > 0`
(Definition 1); `1 ≤ p, q`, `d ≥ 1`. Values in `ℝ≥0∞`. -/
theorem proposition_28 (r : ℝ) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (p q qs rs : ℝ≥0∞) (L α : ℝ), 1 ≤ d → 1 ≤ p → 1 ≤ q →
      q⁻¹ + qs⁻¹ = 1 → (ENNReal.ofReal r)⁻¹ + rs⁻¹ = 1 → 0 < α →
      (∀ g : Fin d → ℝ, RegimeDRCVaR.normM qs g ≤ 1 → RegimeDRCVaR.normM rs g ≤ L) →
      ∀ R : ℝ, 0 < R →
        (sfat (linClassLp p qs d) α : ℝ≥0∞) ≤
          ENNReal.ofReal C * (ENNReal.ofReal ((L * R / α) ^ max 2 r) +
            logN (coverNum p (ENNReal.ofReal r) d R)) := by sorry

end NondualOpt
