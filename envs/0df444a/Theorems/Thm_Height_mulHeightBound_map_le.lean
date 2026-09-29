-- Prove2me | Theorems.Thm_Height_mulHeightBound_map_le
-- name    : Height.mulHeightBound_map_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/59a08bbb-1f40-590c-ad0a-1c007ed8021b
-- title:
--   Behaviour of `mulHeightBound` under extension of the base number field
-- statement:
--   Let $K$ and $L$ be number fields, with $L$ given as a $K$-algebra, and let $\iota$ and $\iota'$ be finite index types. Let $p = (p_j)_{j \in \iota'}$ be a family of polynomials $p_j \in K[X_i : i \in \iota]$ in the variables indexed by $\iota$, with coefficients in $K$. Form the base-changed family by applying the structure map $K \to L$ to the coefficients, i.e. the family $(\mathrm{map}(\mathrm{algebraMap}\,K\,L)(p_j))_{j \in \iota'}$ of polynomials over $L$. The assertion is the inequality
--   $$\mathrm{mulHeightBound}\big((\mathrm{map}(\mathrm{algebraMap}\,K\,L)(p_j))_j\big) \;\le\; \mathrm{mulHeightBound}\big((p_j)_j\big)^{\,[L:K]},$$
--   where $\mathrm{mulHeightBound}$ denotes Mathlib's multiplicative bound attached to a finite family of multivariable polynomials over a number field — the constant by which multiplicative heights may grow under evaluation of the family — and $[L:K]$ is `Module.finrank K L`. Only the inequality is asserted, in the direction needed for transferring height lower bounds along $K \subseteq L$; no hypothesis beyond the standing field and finiteness assumptions is imposed.
--
--   This is the comparison of the polynomial-evaluation height constant under a finite extension of number fields, the multiplicative counterpart of the relation $h_L(\mathrm{algebraMap}\,x) = [L:K]\,h_K(x)$ recorded in [`Height.logHeight_algebraMap`](thm.html#Height.logHeight_algebraMap). It is used in the height estimates on modular curves, specifically by [`ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero`](thm.html#ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero), where a bound proved over a small field must be applied to points with coordinates in a larger one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Height_mulHeightBound_map_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Height.mulHeightBound_map_le {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {ι ι' : Type*} [Finite ι] [Finite ι'] (p : ι' → MvPolynomial ι K) :
    Height.mulHeightBound (fun j => MvPolynomial.map (algebraMap K L) (p j))
      ≤ Height.mulHeightBound p ^ Module.finrank K L := by sorry
