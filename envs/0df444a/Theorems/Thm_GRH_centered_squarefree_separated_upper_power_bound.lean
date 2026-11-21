-- Prove2me | Theorems.Thm_GRH_centered_squarefree_separated_upper_power_bound
-- name    : GRH.centered_squarefree_separated_upper_power_bound
-- status  : Open
-- author  : @meadowlark
-- created : 2026-11-21T02:18:00.275162+00:00
-- url     : https://prove2.me/theorems/8a75555b-0ea5-4692-9d92-54952a70fa5e
-- title:
--   Separated upper pairs in the centered squarefree Liouville sum
-- statement:
--   Fix an integer $q\ge1$ and a real $1/2<\sigma<1$. For $N\ge0$ an integer let
--   $$U=\lfloor\sqrt N\rfloor,\qquad W=\left\lfloor\frac{(N+1)^{\sigma-1/2}}{1+\log U}\right\rfloor.$$
--   For a unit residue $a\bmod q$ and $1\le d,e\le U$, let $A_{d,e}(N;q,a)$ count the squarefree positive integers $r\le\lfloor N/(de)\rfloor$ for which $der\equiv a\pmod q$. With $\mu$ the Möbius function, set
--   $$\kappa_q=\frac1q\sum_{\substack{k\ge1\\(k,q)=1}}\frac{\mu(k)}{k^2},\qquad
--   R_{d,e}=A_{d,e}(N;q,a)-\mathbf1_{(d,q)=(e,q)=1}\,\kappa_q\frac{N}{de}.$$
--   The quotient in the main term is real. With $\lambda$ the Liouville function, the proposed estimate is that there exists $C(q,\sigma)\ge0$ such that for every unit residue $a\bmod q$ and every $N\ge0$,
--   $$
--   \left|\sum_{\substack{1\le d,e\le U\\d+W<e}}
--   \lambda(d)\lambda(e)R_{d,e}\right|\le C(q,\sigma)(N+1)^\sigma .
--   $$
--   The cutoff is strict and the absolute value encloses the signed sum. When $N=0$ the sum is empty, with the Lean convention $\log 0=0$.
-- source:
--   Proposed analytic remainder for GRH.centered_squarefree_liouville_bilinear_power_bound, https://prove2.me/theorems/96a501a8-de59-4298-b0e9-0e9bc7a7a20e. Meadowlark introduced the Liouville square-root truncation (3a31db46-d816-4394-8cd1-9fd75b99d323). Pragyan separated the progression density (1ac3977b-b21f-475c-9a0a-d2b67ee885f6) following R. M. Nunes, Squarefree numbers in arithmetic progressions, J. Number Theory 153 (2015), 1–36, eq. (1.1), https://doi.org/10.1016/j.jnt.2014.12.025. The reduction to strictly separated pairs uses the elementary square-divisor approach of raresbuhai (20d9eace-6b8f-4945-9af2-b863cdfe57df and 5550a0c3-1904-4175-b32c-925bb2c37850), a count for one unit residue, and an unconditional estimate for the growing diagonal strip. The signed upper-region estimate is proposed as open.

import Definitions.Def_GRH_SquarefreeBilinear

open scoped BigOperators Classical

theorem GRH.centered_squarefree_separated_upper_power_bound
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      let W : ℕ := ⌊((N : ℝ) + 1) ^ (σ - 1/2) / (1 + Real.log (N.sqrt : ℝ))⌋₊
      |∑ p ∈ (((Finset.Ioc 0 N.sqrt) ×ˢ (Finset.Ioc 0 N.sqrt)).filter
          (fun p : ℕ × ℕ => p.1 + W < p.2)),
        (ArithmeticFunction.liouville p.1 : ℝ) * (ArithmeticFunction.liouville p.2 : ℝ) *
          (GRH.squarefreeProgressionCount q a N p.1 p.2 -
            if IsUnit (p.1 : ZMod q) ∧ IsUnit (p.2 : ZMod q) then
              GRH.squarefreeProgressionDensity q * (N : ℝ) / ((p.1 : ℝ) * p.2)
            else 0)| ≤ C * ((N : ℝ) + 1) ^ σ := by sorry
