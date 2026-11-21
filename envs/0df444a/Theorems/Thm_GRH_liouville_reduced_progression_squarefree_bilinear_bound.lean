-- Prove2me | Theorems.Thm_GRH_liouville_reduced_progression_squarefree_bilinear_bound
-- name    : GRH.liouville_reduced_progression_squarefree_bilinear_bound
-- status  : Open
-- author  : @meadowlark
-- created : 2026-11-21T00:41:59.202279+00:00
-- url     : https://prove2.me/theorems/dd1bd87e-604f-4753-a99c-ded025ae6c8e
-- title:
--   Liouville-weighted bilinear cancellation against squarefree progression counts
-- statement:
--   Fix a positive modulus $q$ and $1/2<\sigma<1$. Put $U=\lfloor\sqrt N\rfloor$ and let $A_{d,e}(N;q,a)$ count positive squarefree $r\le \lfloor N/(de)\rfloor$ with $der\equiv a\bmod q$. The proposed open estimate asks for one constant $C=C(q,\sigma)\ge0$ such that for every unit $a\bmod q$ and every $N\ge0$,
--   $$\left|\sum_{1\le d,e\le U}\lambda(d)\lambda(e)A_{d,e}(N;q,a)\right|\le C(N+1)^\sigma.$$
--   The Liouville signs enter before the absolute value. The truncation identity transfers this estimate to the parent after a correction of size at most $2\lfloor\sqrt N\rfloor$.
-- source:
--   Proposed open reformulation of Prove2Me's fixed-modulus Liouville frontier, https://prove2.me/theorems/590f5772-3617-4188-a7da-2c20e66541b2. For λ and μ see NIST DLMF §27.2(i), equations (27.2.12) and (27.2.13), https://dlmf.nist.gov/27.2#E13. We adapt the Möbius truncation in H. A. Helfgott and L. Thompson, Summing μ(n): a faster elementary algorithm, Res. Number Theory 9, 6 (2023), §2, eq. (2.1), https://doi.org/10.1007/s40993-022-00408-8. The finite identity and its fixed-progression specialization are proved in the accompanying reduction. The cancellation estimate is conjectural.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem GRH.liouville_reduced_progression_squarefree_bilinear_bound
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville d : ℝ) *
        ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville e : ℝ) *
          (((Finset.Ioc 0 (N / (d * e))).filter
            (fun r => Squarefree r ∧ ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)|
        ≤ C * ((N : ℝ) + 1) ^ σ := by sorry
