-- Prove2me | Theorems.Thm_GreenTao_cs_coefficients
-- name    : GreenTao.cs_coefficients
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T21:27:28.492175+00:00
-- url     : https://prove2.me/theorems/44b476d6-e078-4067-bd95-caee57c93b70
-- title:
--   Height and separation of the progression Cauchy–Schwarz coefficients
-- statement:
--   For $d\ge0$ and $j\in\{0,\ldots,d\}$, let $\sigma_j$ enumerate the positions other than $j$, and put
--
--   $$c_i=\sigma_j(i)-j,\qquad a_{i\ell}=1-c_i/c_\ell.$$
--
--   The integers $c_i$ are nonzero, pairwise distinct, and satisfy $|c_i|\le d$. Each rational coefficient $a_{i\ell}$ has reduced numerator and positive denominator bounded in absolute value by $d$, and
--
--   $$a_{i\ell}=0\quad\Longleftrightarrow\quad i=\ell.$$
--
--   These are the coefficient-height and separation facts needed to apply the existing linear-forms condition to the progression Cauchy–Schwarz forms and their cube copies. For $d=0$, all assertions over indices are vacuous.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5, the forms φ_i(y)=Σ_l(1−c_i/c_l)y_l in the proof of Proposition 5.3 and the coefficient/nonproportionality hypotheses of Definition 3.1. This auxiliary arithmetic lemma makes those checks explicit for consecutive progression coefficients translated to c_j=0.

import Definitions.Def_GreenTao_ProgressionCS
open scoped BigOperators Topology
open Filter GreenTao

theorem GreenTao.cs_coefficients (d : ℕ) (j : Fin (d + 1)) :
    (∀ i : Fin d, csCoeff d j i ≠ 0 ∧ (csCoeff d j i).natAbs ≤ d) ∧
    Function.Injective (csCoeff d j) ∧
    (∀ i l : Fin d, (csRatCoeff d j i l).num.natAbs ≤ d ∧ (csRatCoeff d j i l).den ≤ d) ∧
    (∀ i l : Fin d, csRatCoeff d j i l = 0 ↔ i = l) := by sorry
