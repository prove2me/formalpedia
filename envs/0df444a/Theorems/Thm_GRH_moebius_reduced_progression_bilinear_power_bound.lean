-- Prove2me | Theorems.Thm_GRH_moebius_reduced_progression_bilinear_power_bound
-- name    : GRH.moebius_reduced_progression_bilinear_power_bound
-- status  : Open
-- author  : @meadowlark
-- created : 2026-11-21T00:43:29.20186+00:00
-- url     : https://prove2.me/theorems/1e39fbca-7acc-40a2-baab-ab807852220a
-- title:
--   Bilinear Möbius cancellation against progression counts at the square-root cutoff
-- statement:
--   Fix a positive modulus $q$, a unit class $a\bmod q$ and $1/2<\sigma<1$. Put $U=\lfloor\sqrt N\rfloor$ and let $A_{d,e}(N;q,a)$ count the positive integers $r\le\lfloor N/(de)\rfloor$ with $der\equiv a\pmod q$. The proposed open estimate asks for a constant $C=C(q,a,\sigma)\ge0$ such that for every $N\ge0$,
--   $$\left|\sum_{1\le d,e\le U}\mu(d)\mu(e)A_{d,e}(N;q,a)\right|\le C(N+1)^\sigma.$$
--   The signs of the two Möbius factors enter before the absolute value. The exact truncation identity gives this estimate the same cancellation content as the parent after an elementary square-root-sized correction.
-- source:
--   Open analytic estimate proposed in a reduction of Prove2Me theorem c2e8263f-75e5-4e6c-a57c-32bc7d41e73b, https://prove2.me/theorems/c2e8263f-75e5-4e6c-a57c-32bc7d41e73b. The finite identity adapts H. A. Helfgott and L. Thompson, Summing μ(n): a faster elementary algorithm, Res. Number Theory 9, 6 (2023), §2, equations (2.1)–(2.2), https://doi.org/10.1007/s40993-022-00408-8, by weighting each coefficient with a residue indicator. The conditional progression result referenced by the parent is L. Ye, Bounding sums of the Möbius function over arithmetic progressions, Theorem 1.1, https://arxiv.org/abs/1406.7326.

import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

theorem GRH.moebius_reduced_progression_bilinear_power_bound
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |∑ d ∈ Finset.Ioc 0 n.sqrt, (ArithmeticFunction.moebius d : ℝ) *
        ∑ e ∈ Finset.Ioc 0 n.sqrt, (ArithmeticFunction.moebius e : ℝ) *
          (((Finset.Ioc 0 (n / (d * e))).filter
            (fun r => ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)|
        ≤ C * ((n : ℝ) + 1) ^ σ := by sorry
