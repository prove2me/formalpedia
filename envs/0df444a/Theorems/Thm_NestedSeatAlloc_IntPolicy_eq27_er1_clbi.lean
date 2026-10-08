-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_eq27_er1_clbi
-- name    : NestedSeatAlloc.IntPolicy.eq27_er1_clbi
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:38:28.714818+00:00
-- url     : https://prove2.me/theorems/21543cdb-2cef-4c0d-8b7e-2981bdb2cf31
-- title:
--   (27), p. 132 — δER₁[s; p; X] = [f₁Pr[X₁ > s], f₁Pr[X₁ ≥ s]], and ER₁ is CLBI for integer demand
-- statement:
--   Work in the seat model: independent nonnegative demands $X_1, X_2, \dots$ on a probability space $(\Omega, \mathcal F, P)$ and strictly decreasing fares $f_1 > f_2 > \cdots$. Assume the demands are integer valued and $f_1 \ge 0$. Let $ER_1[s; p; X] = f_1\,E[\min(s, X_1)]$ be the expected revenue of the highest fare class with $s$ seats available (it does not depend on the policy $p$). Then:
--
--   1. $ER_1[\,\cdot\,; p; X]$ is CLBI: concave on $s \ge 0$ and linear on every interval $[m, m+1]$, $m = 0, 1, 2, \dots$;
--   2. for every $s \ge 0$ its right derivative is
--   $$\delta_+ ER_1[s; p; X] = f_1 \Pr[X_1 > s];$$
--   3. for every $s > 0$ its left derivative is
--   $$\delta_- ER_1[s; p; X] = f_1 \Pr[X_1 \ge s].$$
--
--   Items 2 and 3 are equation (27), $\delta ER_1[s; p; X] = [f_1 \Pr[X_1 > s], f_1 \Pr[X_1 \ge s]]$. This is the base case of the induction that proves Theorem 2.
--
--   **Formalization Note** The hypothesis $f_1 \ge 0$ is added: if $f_1 < 0$ and $X_1$ is not almost surely $0$, then $f_1 E[\min(s, X_1)]$ is convex and not concave, so the CLBI claim fails. The paper's fares are average revenues per booking, hence positive. At $s = 0$ the left derivative is the convention $+\infty$ and is not stated.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), (27) and the sentence following it, proof of Theorem 2, p. 132

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

/-- (27), p. 132, and "ER₁ is CLBI": with integer-valued demand and a nonnegative top fare, `ER_1[s; p; X]`
is CLBI on `s ≥ 0`, its right derivative at `s ≥ 0` is `f₁ Pr[X₁ > s]`, and its left derivative at `s > 0` is
`f₁ Pr[X₁ ≥ s]`. -/
theorem eq27_er1_clbi {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (hf1 : 0 ≤ f 1) :
    IsCLBI (expRevenue P X f p 1) ∧
      (∀ s, 0 ≤ s →
        HasDerivWithinAt (expRevenue P X f p 1) (f 1 * P.real {ω | s < X 1 ω}) (Set.Ici s) s) ∧
      (∀ s, 0 < s →
        HasDerivWithinAt (expRevenue P X f p 1) (f 1 * P.real {ω | s ≤ X 1 ω}) (Set.Iic s) s) := by sorry

end NestedSeatAlloc.IntPolicy
