-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_Supplement_theorem_12
-- name    : OptInapprox.Bal2Sat.Supplement.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:03:35.551802+00:00
-- url     : https://prove2.me/theorems/5bd68601-5ad1-4eeb-8829-629514f3049e
-- title:
--   Theorem 12 — UGC gap hardness for MAX-2LIN(q), including difference equations
-- statement:
--   Assume the published Unique Games Conjecture. For every integer $q\ge2$, every $\rho\in[0,1]$ and every $\varepsilon>0$, define
--
--   $$c=\rho+\frac{1-\rho}{q}-\varepsilon,\qquad s=q\Lambda_\rho(1/q)+\varepsilon.$$
--
--   It is NP-hard to distinguish MAX-2LIN$(q)$ instances with optimum satisfied fraction at least $c$ from those with optimum fraction at most $s$. The same gap hardness holds even when every equation has the form $x_i-x_j=c_{ij}$ modulo $q$. Both clauses are explicit; the difference subclass embeds into the general equation class with coefficients $1,-1$.
--
--   Here $\Lambda_\rho(\mu)$ is the published correlated Gaussian upper-orthant probability at marginal mass $\mu$ (Definition 8). Since $q\ge2$, the argument $1/q$ lies strictly between zero and one, so its threshold is defined. Composite alphabets, both correlation endpoints and every positive error are included. The statement uses the published UGC gap-reduction convention even where the two numerical promises overlap; it adds no separation premise. The cited analytic and central-limit results are proof obligations, not additional assumptions.
--
--   Differences from the source:
--   - encoding: nonnegative weighted linear equations modulo any q≥2 → nonempty unit-weight lists with arbitrary modular coefficients, and a separate difference list with an explicit inclusion; reason: hardness on the encodable subclass implies hardness on the source problem; missing variables permit equations with fewer than two variables
--   - encoding: optimum fraction → finite maximum divided by the positive number of listed equations; reason: the nonempty-list promise excludes only the undefined zero-total-weight case
--   - reading: NP-hard to distinguish for all stated parameters → the published OptInapprox.MaxCut.GapNPHard for both equation classes, with ρ=0,1 and overlapping numerical promises retained; reason: this is exactly the gap convention of the published UGC; no stronger disjointness or parameter-separation claim is assumed
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 15, Theorem 12; Definitions 14–15 p. 27; proof pp. 33–35, §11.4

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Supplement_LinearCSP
import Definitions.Def_OptInapprox_Orthant_Setting

namespace OptInapprox.Bal2Sat.Supplement

theorem theorem_12 (hUGC : OptInapprox.MaxCut.UGC) (q : ℕ) (hq : 2 ≤ q)
    (ρ ε : ℝ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hε : 0 < ε) :
    letI : NeZero q := ⟨by omega⟩
    let c := ρ + (1 - ρ) / q - ε
    let s := (q : ℝ) * OptInapprox.Orthant.Lambda ρ (1 / q) + ε
    LinearGapHard q c s ∧ DifferenceGapHard q c s := by sorry

end OptInapprox.Bal2Sat.Supplement
