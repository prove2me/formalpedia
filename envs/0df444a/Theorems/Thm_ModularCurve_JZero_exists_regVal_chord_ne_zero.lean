-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_regVal_chord_ne_zero
-- name    : ModularCurve.JZero.exists_regVal_chord_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/f0ffe815-9612-5c46-a371-e6a153441c88
-- title:
--   Non-vanishing chord datum for an embedding basis
-- statement:
--   Fix $N$ with $N \neq 0$ and work in the field $F =$ `modularFunctionFieldBar N`, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image, under the coefficient embedding, of the field `modularFunctionFieldFull N` obtained by adjoining the divisor expansions of level $N$ to $\mathbb{Q}$. Let $r$ be a natural number and $s : \mathrm{Fin}\ r \to F$ a family satisfying `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the Riemann–Roch space $\{f : v(f) \le \exp(D(v)) \text{ for all places } v\}$ of the divisor $D =$ `embDivisor N`$= (\mathrm{embDegree}\ N)\cdot \overline{\infty}$, the multiple of the cusp at infinity. Let $v_0$ be a place of $F$ over $\overline{\mathbb{Q}}$ (a proper valuation subring containing $\overline{\mathbb{Q}}$ whose ring is a principal ideal ring) and let $t \in F$ satisfy $\mathrm{ord}_{v_0}(t) = 1$, i.e. $t$ is a uniformiser at $v_0$. Write $\mathrm{piv}$ for the index `pivotIndex s v₀`, chosen so that $\mathrm{ord}_{v_0}(s_{\mathrm{piv}})$ is minimal among the $\mathrm{ord}_{v_0}(s_j)$ when such a minimum exists, and $x_i =$ `evalVec s v₀ i` $= \mathrm{ev}_{v_0}(s_i / s_{\mathrm{piv}})$, the residue at $v_0$ of the pivot-normalised coordinate. The assertion is that there exists a pair of indices $(i,j)$ with
--   $$\mathrm{ev}_{v_0}\!\left(\frac{x_i\, s_j - x_j\, s_i}{s_{\mathrm{piv}}\, t}\right) \neq 0,$$
--   this being the value `regVal s v₀ t 1 1` of the chord function $x_i s_j - x_j s_i$; here $\mathrm{ev}_{v_0}$ denotes the evaluation `Place.evalAt`, the residue map on the valuation subring transported to $\overline{\mathbb{Q}}$ and extended by $0$ outside it. In particular the existence of such a pair forces $r > 0$.
--
--   This is the statement that the map to projective space given by the complete linear system of $(\mathrm{embDegree}\ N)\cdot\overline{\infty}$ on $X_0(N)$ separates tangent vectors at every place: some chord coordinate $x_i s_j - x_j s_i$ vanishes at $v_0$ to order exactly one in the pivot trivialisation. It discharges the non-degeneracy side condition in the regularised Jensen-type estimates and in the jet computations on $J_0(N)$, and is cited by [`ModularCurve.JZero.exists_ord_div_sub_evalAt_eq_one`](thm.html#ModularCurve.JZero.exists_ord_div_sub_evalAt_eq_one), [`ModularCurve.JZero.jensen_bad_primes_of_prime_of_five_le`](thm.html#ModularCurve.JZero.jensen_bad_primes_of_prime_of_five_le) and [`ModularCurve.JZero.sum_pairHt_le_of_isUnit_det_jetMatrix`](thm.html#ModularCurve.JZero.sum_pairHt_le_of_isUnit_det_jetMatrix).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_regVal_chord_ne_zero.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_regVal_chord_ne_zero (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (t : modularFunctionFieldBar N) (ht : v₀.ord t = 1) :
    ∃ p : Fin r × Fin r,
      regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1) ≠ 0 := by sorry
